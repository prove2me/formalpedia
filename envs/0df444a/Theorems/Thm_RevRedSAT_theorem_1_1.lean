-- Prove2me | Theorems.Thm_RevRedSAT_theorem_1_1
-- name    : RevRedSAT.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:37.523196+00:00
-- url     : https://prove2.me/theorems/076cf24e-4cae-49ba-9810-46cccf78c067
-- title:
--   Theorem 1.1 — Vertex Cover and d-Hitting Set in $2^{o(k)}|I|^{O(1)}$ under Subexponential 3-SAT, with explicit rates under Quantitative d-SAT
-- statement:
--   1. Under the Subexponential 3-SAT Assumption (4.1):
--      1. Vertex Cover has a deterministic algorithm solving the search problem in $2^{g(k)}|w|^{c}$ steps, with $g(k)/k\to0$;
--      2. there is one exponent $c$ such that for every fixed $d\ge2$, $d$-Hitting Set has a deterministic algorithm solving the search problem in $2^{g_d(k)}|w|^{c}$ steps, with $g_d(k)/k\to0$.
--   2. Under the Quantitative $d$-SAT Assumption (4.2):
--      1. Vertex Cover has a deterministic algorithm with running time
--      $$\bigl\lfloor 2^{C\,k\eta(k)/\sqrt{\lambda(k)}}\,|w|^{c}\bigr\rfloor;$$
--      2. there is one exponent $c$ such that for every fixed $d\ge2$, $d$-Hitting Set has a deterministic algorithm with running time
--      $$\bigl\lfloor 2^{C_d\,k\eta(k)^2/\sqrt{\lambda(k)}}\,|w|^{c}\bigr\rfloor;$$
--      3. there is one exponent $c$ such that for every fixed $d\ge2$, $d$-Hitting Set has a randomized algorithm with the same form of running time that has no false positives and succeeds with probability at least $2/3$ on a YES-instance.
--
--   Here $k$ is the solution budget, $w$ any code of the instance, $\lambda(t)=\log_2(t+2)$ and $\eta(t)=\log_2\log_2(t+4)$. Every algorithm returns a solution whenever one exists.
--
--   The theorem transfers the assumed subexponential SAT algorithms to the two basic parameterized covering problems with the budget $k$ as the only exponential parameter; for $d\ge3$ the known element kernels are too large for a direct encoding.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - reading: an algorithm for the problem (Table 1: 'Det.; search') → a search algorithm: output 'no' exactly on NO-instances, otherwise the list of a feasible solution; reason: Table 1, App. C and the proofs (solution recovery) state search; the decision-only reading is weaker
--   - encoding: 2^{o(k)} → 2^{g(k)} for one g : ℕ → ℕ with g(k)/k → 0, chosen with the machine before the instance; reason: the definition of o(k); no rate of convergence is asked
--   - encoding: 2^{O(k log log k/√log k)} and 2^{O_d(k(log log k)²/√log k)} → ⌊2^{C·kη(k)/√λ(k)}·|w|^c⌋ and ⌊2^{C_d·kη(k)²/√λ(k)}·|w|^c⌋; reason: the paper's own V(k), C(k) (p.8) and Theorems 5.3, 6.13; the two forms differ by factors tending to 1 and the displayed rates concern sufficiently large inputs (p.3), so they define the same 2^{O(·)} class
--   - reading: |I|^{O(1)} → one exponent c for every d ≥ 2, chosen before d; reason: an unsubscripted O is absolute (§3, p.27); Theorems 6.7, 6.13 and Lemma 6.6 say the exponent is absolute
--   - encoding: a randomized algorithm with no false positives, success probability at least 2/3 → MonteCarloWithin with θ = 2/3: ρ(t) random bits (ρ computable, t the time bound) read after the input, sound on every string, success on a 2/3 fraction of strings; reason: the uniform measure on random strings; worst-case time on every string
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 1.1, p.3 (printed) = PDF p.5

import Mathlib
import Definitions.Def_RevRedSAT_SubexpThreeSAT
import Definitions.Def_RevRedSAT_QuantDSAT
import Definitions.Def_RevRedSAT_VCInstance
import Definitions.Def_RevRedSAT_IsHSCode

set_option autoImplicit false

namespace RevRedSAT

open Filter Topology

/-- **Theorem 1.1 (Vertex Cover and d-Hitting Set from faster SAT).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 1.1, p.3: "Under the Subexponential 3-SAT Assumption, Vertex Cover and, for every fixed
d ≥ 2, d-Hitting Set admit deterministic 2^{o(k)}|I|^{O(1)}-time algorithms, parameterized by the
solution budget k. Under the Quantitative d-SAT Assumption: • Vertex Cover admits a deterministic
algorithm with running time 2^{O(k log log k/√log k)}|I|^{O(1)}. • For every fixed d ≥ 2, d-Hitting
Set admits both deterministic and (simpler) randomized algorithms with running time
2^{O_d(k(log log k)²/√log k)}|I|^{O(1)}. The randomized algorithm has no false positives and
succeeds with probability at least 2/3 on a YES-instance."

1. Under Assumption 4.1: a machine solves the Vertex Cover search problem within `2^{g(k)}·|w|^c`
   with `g(k)/k → 0`; and there is one exponent `c` such that for every `d ≥ 2` a machine solves the
   `d`-Hitting Set search problem within `2^{g_d(k)}·|w|^c`, `g_d(k)/k → 0`.
2. Under Assumption 4.2: a machine solves Vertex Cover within `⌊2^{C·kη(k)/√λ(k)}·|w|^c⌋`; there is
   one exponent `c` such that for every `d ≥ 2` a machine solves `d`-Hitting Set within
   `⌊2^{C_d·kη(k)²/√λ(k)}·|w|^c⌋`; and there is one exponent `c` such that for every `d ≥ 2` a
   Monte Carlo machine without false positives and with success probability at least `2/3` does so
   within the same form of bound.

**Formalization Note** Algorithms are finite-alphabet Mathlib TM2 machines (`FiniteAlphabets`); a
search algorithm outputs `[false]` exactly on NO-instances and otherwise the list of a solution
(`IsSearchOutput`, App. C, Table 1). `2^{o(k)}` is `2^{g(k)}` for one `g` with `g(k)/k → 0`, chosen
with the machine before the instance. The rates are written with `λ(t) = log₂(t + 2)` and
`η(t) = log₂ log₂(t + 4)` as in Table 1's `V(k)`, `C(k)` (p.8) and Theorems 5.3, 6.13; they differ
from the printed `log log k/√log k` forms by factors tending to `1` and are defined at every `k`.
The polynomial exponent is absolute (an unsubscripted `O`, §3); only the exponential constant and
`g` depend on `d`. The bound holds on every code of every instance. -/
theorem theorem_1_1 :
    (SubexpThreeSAT →
      (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
        ∃ (c : ℕ) (g : ℕ → ℕ), Tendsto (fun k => (g k : ℝ) / k) atTop (𝓝 0) ∧
          SearchWithin M VCInstance.n IsVCCode VCValid (fun I w => 2 ^ g I.k * w.length ^ c)) ∧
      (∃ c : ℕ, ∀ d : ℕ, 2 ≤ d →
        ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
          ∃ g : ℕ → ℕ, Tendsto (fun k => (g k : ℝ) / k) atTop (𝓝 0) ∧
            SearchWithin M HSElemKernel.HSInstance.n (IsDHSCode d) HSValid
              (fun I w => 2 ^ g I.k * w.length ^ c))) ∧
    (QuantDSAT →
      (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
        ∃ (C : ℝ) (c : ℕ),
          SearchWithin M VCInstance.n IsVCCode VCValid
            (fun I w => expBound (vcRate C I.k) w.length c)) ∧
      (∃ c : ℕ, ∀ d : ℕ, 2 ≤ d →
        ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
          SearchWithin M HSElemKernel.HSInstance.n (IsDHSCode d) HSValid
            (fun I w => expBound (hsRate C I.k) w.length c)) ∧
      (∃ c : ℕ, ∀ d : ℕ, 2 ≤ d →
        ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
          MonteCarloWithin M HSElemKernel.HSInstance.n (IsDHSCode d) HSValid
            (fun I w => expBound (hsRate C I.k) w.length c) (2 / 3))) := by sorry

end RevRedSAT
