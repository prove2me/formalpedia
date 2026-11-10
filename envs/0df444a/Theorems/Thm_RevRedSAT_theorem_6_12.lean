-- Prove2me | Theorems.Thm_RevRedSAT_theorem_6_12
-- name    : RevRedSAT.theorem_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:57.960879+00:00
-- url     : https://prove2.me/theorems/449f165a-c6fb-40c4-968d-a218fdf5c5a8
-- title:
--   Theorem 6.12 — a randomized $2^{O_d(k\eta(k)^2/\sqrt{\lambda(k)})}|I|^{O(1)}$ algorithm with success 3/4
-- statement:
--   For every polynomial exponent $c_0$ there is an exponent $c$ such that for every fixed $d\ge2$: if one algorithm decides every CNF formula of width at most $\max\{3,2d\}$ within the bound of the Quantitative $d$-SAT Assumption with polynomial exponent $c_0$, then there are a randomized algorithm and a constant $C_d$ for $d$-Hitting Set with running time
--
--   $$\bigl\lfloor 2^{C_d\,k\eta(k)^2/\sqrt{\lambda(k)}}\,|w|^{c}\bigr\rfloor$$
--
--   on every random string; on a yes-instance it returns a hitting set of size at most $k$ with probability at least $3/4$, and on a no-instance it always returns no.
--
--   Under Assumption 4.2 the hypothesis holds for every $d$ with one exponent $c_0$, which gives the theorem as printed.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - generalization: under the Quantitative d-SAT Assumption; 'It uses SAT formulas of width at most max{3, 2d}' → for every exponent c₀ there is c such that for every d ≥ 2 the premise is Assumption 4.2's bound for widths ≤ max{3, 2d} with exponent c₀ (QuantSATUpTo); reason: Assumption 4.2 implies the premise for every d with its own exponent c₀, so the source's theorem, with an absolute exponent, is the special case
--   - encoding: a randomized algorithm with no false positives and success probability 3/4 → MonteCarloWithin: ρ(t) random bits (ρ computable, t the time bound) read after the input, sound on every string, success on a 3/4 fraction of strings; reason: the uniform measure on random strings; worst-case time on every string
--   - reading: |I|^{O(1)} → one exponent c for every d ≥ 2, chosen before d; reason: an unsubscripted O is absolute (§3, p.27); Theorems 6.7, 6.13 and Lemma 6.6 say the exponent is absolute
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.12, p.44 (printed) = PDF p.46

import Mathlib
import Definitions.Def_RevRedSAT_QuantDSAT
import Definitions.Def_RevRedSAT_IsHSCode

set_option autoImplicit false

namespace RevRedSAT

/-- **Theorem 6.12 (two random buckets per element).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.12, p.44: "Under the Quantitative d-SAT Assumption, for every fixed d ≥ 2 there is a
randomized algorithm for d-Hitting Set with running time 2^{O_d(kη(k)²/√λ(k))}|I|^{O(1)}. On a
yes-instance it returns a hitting set of size at most k with probability at least 3/4; on a
no-instance it always returns no. It uses SAT formulas of width at most max{3, 2d}."

For every polynomial exponent `c₀` of a SAT algorithm there is an exponent `c` such that for every
`d ≥ 2`: if one finite-alphabet machine decides all formulas of width at most `max{3, 2d}` within the
bound of Assumption 4.2 with exponent `c₀` (`QuantSATUpTo`), then a Monte Carlo machine without
false positives and with success probability at least `3/4` solves `d`-Hitting Set within
`⌊2^{C_d·kη(k)²/√λ(k)}·|w|^c⌋`.

**Formalization Note** The last sentence of the theorem is read as: the premise is needed only for
widths at most `max{3, 2d}`. `QuantDSAT` gives `QuantSATUpTo w c₀` for every `w` with its own
exponent `c₀`, so this specializes to the theorem as stated under Assumption 4.2, with `c`
absolute. -/
theorem theorem_6_12 :
    ∀ c₀ : ℕ, ∃ c : ℕ, ∀ d : ℕ, 2 ≤ d → QuantSATUpTo (max 3 (2 * d)) c₀ →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
        MonteCarloWithin M HSElemKernel.HSInstance.n (IsDHSCode d) HSValid
          (fun I w => expBound (hsRate C I.k) w.length c) (3 / 4) := by sorry

end RevRedSAT
