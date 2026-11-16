-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_Supplement_psp_lower_bound
-- name    : WatsonPseudodeterminism.MASeparation.Supplement.psp_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:32:08.593349+00:00
-- url     : https://prove2.me/theorems/57ed4195-a1df-4b17-b444-7458e08e67f2
-- title:
--   §3 — Square-root psP lower bound at error 0.01
-- statement:
--   Let $F_n=f\circ g^n$ be the §3 function with $h=100\lceil\log_2 n\rceil$, over the sizes $n=4s^2$, $s\ge1$. There is a natural threshold $n_0$ such that for every such $n\ge n_0$ and every natural $d$,
--   $$d\le 0.01\sqrt n\ \Longrightarrow\ F_n\text{ has no }0.01\text{-error psP-type protocol of cost }d.$$
--   Here a $0.01$-error psP-type protocol is one distribution over trees of depth at most $d$ whose acceptance probability lies in $[0,0.01]\cup[0.99,1]$ on every input, at least $0.99$ on valid 1-inputs and at most $0.01$ on valid 0-inputs; equivalently, a total $F'$ agreeing with $F_n$ has a $0.01$-error randomized protocol of cost $d$.
--
--   This is the "$F\notin\mathrm{psP}$" half of Theorem 1, once combined with psP amplification.
--
--   Differences from the source:
--   - reading: h = 100 log n → h = 100 * Nat.clog 2 n, with logarithms to base two; reason: block lengths are integral; this is the base mission's published gadget length, rounding upward preserves the small-discrepancy regime
--   - reading: the implicit sizes n for which n/2 and √n are integers in §3 → n = 4s² for a positive natural s (base predicate Admissible); reason: §3 splits z into halves of length n/2 and flips √n bits per safe iteration; this fixes one infinite sequence on which both are integral
--   - encoding: a total F′ agreeing with F with a randomized protocol D of two-sided error 0.01 → a 0.01-error psP-type protocol (acceptance in [0,0.01] ∪ [0.99,1] on every input); reason: equivalent: given F′ and D the gap holds on every input; given the gap, F′(x,y) = [D(x,y) ≥ 0.99] is total and agrees with F (p. 1 remark)
--   - reading: the proof assumes cost d = 0.01√n and uses large-n numerical estimates → for all admissible n ≥ some n₀, every natural d ≤ 0.01√n is impossible; reason: depth bounds are monotone, so cost exactly 0.01√n covers smaller d; the proof's inequalities (e.g. n/2 − 0.02n − (n/3 + √n) ≥ 0.1n) need n large
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §3, "F ∉ psP", pp. 8–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Supplement_Models
import Definitions.Def_WatsonPseudodeterminism_MASeparation_Supplement_ZPPFunction

namespace WatsonPseudodeterminism.MASeparation.Supplement

/-- §3, pp. 8–10, "F ∉ psP": for all large admissible n, no 0.01-error psP-type protocol of
cost at most 0.01√n computes the §3 function. -/
theorem psp_lower_bound :
    ∃ n₀ : ℕ, ∀ n : ℕ, Admissible n → n₀ ≤ n → ∀ d : ℕ,
      (d : ℝ) ≤ (0.01 : ℝ) * Real.sqrt (n : ℝ) →
      ¬ PsPProtocolErr (0.01 : ℝ) (zppLiftedFn n) d := by sorry

end WatsonPseudodeterminism.MASeparation.Supplement
