-- Prove2me | Theorems.Thm_RevRedSAT_theorem_6_13
-- name    : RevRedSAT.theorem_6_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:33.354723+00:00
-- url     : https://prove2.me/theorems/fca79f7f-b637-4561-a6c2-020f4e244970
-- title:
--   Theorem 6.13 — a deterministic $2^{O_d(k\eta(k)^2/\sqrt{\lambda(k)})}|I|^{O(1)}$ algorithm for d-Hitting Set
-- statement:
--   For every polynomial exponent $c_0$ there is an exponent $c$ such that for every fixed $d\ge2$: if one algorithm decides every CNF formula of width at most $\max\{3,2d\}$ within the variable-based bound $\lfloor 2^{C\,d'^2N\eta(N)/\sqrt{\lambda(N)}}|F|^{c_0}\rfloor$ (width $d'$), then there are a deterministic algorithm and a constant $C_d$ that decide whether a $d$-Hitting Set instance has a hitting set of size at most $k\ge0$, and find one if it exists, within
--
--   $$\bigl\lfloor 2^{C_d\,k\eta(k)^2/\sqrt{\lambda(k)}}\,|w|^{c}\bigr\rfloor\ \text{steps}.$$
--
--   The polynomial exponent $c$ on the original input length is absolute. Under Assumption 4.2 the hypothesis holds for every $d$, which gives the theorem as printed.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - reading: an algorithm for the problem (Table 1: 'Det.; search') → a search algorithm: output 'no' exactly on NO-instances, otherwise the list of a feasible solution; reason: Table 1, App. C and the proofs (solution recovery) state search; the decision-only reading is weaker
--   - generalization: under the Quantitative d-SAT Assumption; 'uses only the variable-based SAT bound for CNF formulas of width at most max{3, 2d}' → for every exponent c₀ there is c such that for every d ≥ 2 the premise is the variable-based bound for widths ≤ max{3, 2d} with exponent c₀ (VarSATUpTo); reason: Assumption 4.2 implies the premise for every d with one exponent c₀, so the source's theorem is the special case
--   - reading: |I|^{O(1)} → one exponent c for every d ≥ 2, chosen before d; reason: an unsubscripted O is absolute (§3, p.27); Theorems 6.7, 6.13 and Lemma 6.6 say the exponent is absolute
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.13, p.45 (printed) = PDF p.47

import Mathlib
import Definitions.Def_RevRedSAT_QuantDSAT
import Definitions.Def_RevRedSAT_IsHSCode

set_option autoImplicit false

namespace RevRedSAT

/-- **Theorem 6.13 (deterministic two-choice algorithm).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.13, p.45: "Assume the Quantitative d-SAT Assumption. For every fixed d ≥ 2, one can
decide whether a d-Hitting Set instance has a hitting set of size at most k ≥ 0, and find one if it
exists, deterministically in time Ĥ_d(k)|I|^{O(1)}, where Ĥ_d(k) = 2^{O_d(kη(k)²/√λ(k))}. The
polynomial exponent on the original input length is absolute. The algorithm uses only the
variable-based SAT bound for CNF formulas of width at most max{3, 2d}."

For every polynomial exponent `c₀` of a SAT algorithm there is an exponent `c` such that for every
`d ≥ 2`: if one finite-alphabet machine decides all formulas of width at most `max{3, 2d}` within
the variable-based bound `⌊2^{C·d²Nη(N)/√λ(N)}·|F|^{c₀}⌋` (`VarSATUpTo`), then a deterministic
machine solves the `d`-Hitting Set search problem within `⌊2^{C_d·kη(k)²/√λ(k)}·|w|^c⌋`.

**Formalization Note** The last sentence is read as: the premise is the variable-based bound for
widths at most `max{3, 2d}` only. `QuantDSAT` gives `VarSATUpTo w c₀` for every `w`, so this
specializes to the theorem under Assumption 4.2, with `c` absolute. -/
theorem theorem_6_13 :
    ∀ c₀ : ℕ, ∃ c : ℕ, ∀ d : ℕ, 2 ≤ d → VarSATUpTo (max 3 (2 * d)) c₀ →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
        SearchWithin M HSElemKernel.HSInstance.n (IsDHSCode d) HSValid
          (fun I w => expBound (hsRate C I.k) w.length c) := by sorry

end RevRedSAT
