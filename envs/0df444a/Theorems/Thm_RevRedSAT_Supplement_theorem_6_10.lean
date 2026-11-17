-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_6_10
-- name    : RevRedSAT.Supplement.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:01:12.724324+00:00
-- url     : https://prove2.me/theorems/161ff96d-221f-43cf-a361-244fcda2f6d5
-- title:
--   Theorem 6.10 — randomized d-Hitting Set in $2^{O_d(k\eta(k)/\lambda(k)^{1/4})}|I|^{O(1)}$ with success 3/4
-- statement:
--   For every polynomial exponent $c_0$ there is an exponent $c$ such that for every fixed $d\ge2$ the following holds. Suppose one algorithm decides every CNF formula of width at most $\max\{3,d\}$ within the bound of the Quantitative $d$-SAT Assumption with polynomial exponent $c_0$. Then there are a randomized algorithm and a constant $C_d$ for $d$-Hitting Set with running time
--
--   $$\Bigl\lfloor 2^{C_d\,k\eta(k)/\lambda(k)^{1/4}}\,|w|^{c}\Bigr\rfloor$$
--
--   on every random string. On a yes-instance it returns a hitting set of size at most $k$ with probability at least $3/4$, and on a no-instance it always returns no.
--
--   Under Assumption 4.2 the hypothesis holds for every $d$ with one exponent $c_0$, which gives the theorem as printed. The one-bucket algorithm is weaker than the two-choice algorithms of Theorems 6.12 and 6.13.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - generalization: under the Quantitative d-SAT Assumption; 'It uses SAT formulas of width at most max{3, d}' → for every exponent c₀ there is c such that for every d ≥ 2 the premise is Assumption 4.2's bound for widths ≤ max{3, d} with exponent c₀ (QuantSATUpTo); reason: Assumption 4.2 implies the premise for every d with its own exponent c₀, so the source's theorem, with an absolute exponent, is the special case
--   - encoding: a randomized algorithm with no false positives and the stated success probability → MonteCarloWithin (EdgeMonteCarloWithin for edge-set solutions): ρ(t) random bits (ρ computable) read after the input, sound on every string, success on the stated fraction of strings; reason: the uniform measure on random strings; worst-case time on every string
--   - reading: |I|^{O(1)} → one exponent c for every d ≥ 2, chosen before d; reason: an unsubscripted O is absolute (§3, p.27)
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.10, p.43 (printed) = PDF p.45

import Mathlib
import Definitions.Def_RevRedSAT_QuantDSAT
import Definitions.Def_RevRedSAT_IsHSCode

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Theorem 6.10 (one random bucket per element).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.10, p.43: "Under the Quantitative d-SAT Assumption, for every fixed d ≥ 2 there is a
randomized algorithm for d-Hitting Set with running time 2^{O_d(kη(k)/λ(k)^{1/4})}|I|^{O(1)}. On a
yes-instance it returns a hitting set of size at most k with probability at least 3/4; on a
no-instance it always returns no. It uses SAT formulas of width at most max{3, d}."

For every polynomial exponent `c₀` of a SAT algorithm there is an exponent `c` such that for every
`d ≥ 2`: if one finite-alphabet machine decides all formulas of width at most `max{3, d}` within
the bound of Assumption 4.2 with exponent `c₀` (`RevRedSAT.QuantSATUpTo`), then a Monte Carlo
machine without false positives and with success probability at least `3/4` solves `d`-Hitting Set
within `⌊2^{C_d·kη(k)/λ(k)^{1/4}} · |w|^c⌋` steps on every random string.

**Formalization Note** The shape of the published `RevRedSAT.theorem_6_12`: the last sentence is
read as "the premise is needed only for widths at most max{3, d}"; Assumption 4.2 gives
`QuantSATUpTo w c₀` for every `w` with its own `c₀`, so this specializes to the theorem under
Assumption 4.2 with an absolute exponent `c`. -/
theorem theorem_6_10 :
    ∀ c₀ : ℕ, ∃ c : ℕ, ∀ d : ℕ, 2 ≤ d → QuantSATUpTo (max 3 d) c₀ →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
        MonteCarloWithin M HSElemKernel.HSInstance.n (IsDHSCode d) HSValid
          (fun I w => expBound (C * I.k * eta I.k / lam I.k ^ ((1 : ℝ) / 4)) w.length c)
          (3 / 4) := by sorry

end RevRedSAT.Supplement
