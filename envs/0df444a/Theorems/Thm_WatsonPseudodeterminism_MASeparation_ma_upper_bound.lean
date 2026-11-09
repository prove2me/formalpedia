-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_ma_upper_bound
-- name    : WatsonPseudodeterminism.MASeparation.ma_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:41:00.755465+00:00
-- url     : https://prove2.me/theorems/3a88f60c-a6b1-4fb8-8460-1995b67110ad
-- title:
--   §4 — Logarithmic MA cost of the separating function
-- statement:
--   Let $h(n)=100\lceil\log_2n\rceil$ and let $F_n=f_n\circ g^n$ be the partial function of §4. Along the admissible sequence $n=4s^2$, $s\ge1$, there is one natural constant $C$ such that
--
--   $$\forall n\ \exists d\le C(\lceil\log_2n\rceil+1):\ F_n\text{ has an MA-type protocol of cost }d.$$
--
--   Every protocol has at most $2^d$ witnesses and depth at most $d$, with completeness $2/3$ and soundness $1/3$. This is the upper bound entering the class separation; it does not postulate correctness of a particular candidate protocol. The source exhibits a randomized left-half test and one test for each right-half coordinate.
--
--   Differences from the source:
--   - reading: h = 100 log n → h = 100 * Nat.clog 2 n, with logarithms to base two; reason: block lengths are integral; rounding upward preserves the small-discrepancy regime specified in the brief
--   - reading: the implicit infinite sequence of even square sizes in §4 → n = 4s² for a positive natural s; reason: this fixes one infinite sequence on which both halves and the square-root block steps are integral
--   - encoding: a set of at most 2^d distributions over depth-d protocols → an indexed family of k PMFs with k ≤ 2^d and support depth at most d; reason: duplicate indices do not change the represented set; every source distribution is represented and zero-mass trees do not affect the law
--   - encoding: O(log n) → one natural C with cost at most C(clog₂ n + 1); reason: the additive one covers short lengths without changing the logarithmic order
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §4, “F ∈ MA”, p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_SeparatingFunction

namespace WatsonPseudodeterminism.MASeparation

/-- §4, p. 10: uniform O(log n) MA cost for the source's separating functions. -/
theorem ma_upper_bound :
    ∃ C : ℕ, ∀ n : ℕ, Admissible n → ∃ d : ℕ,
      d ≤ C * (Nat.clog 2 n + 1) ∧ MAProtocol (liftedFn n) d := by sorry

end WatsonPseudodeterminism.MASeparation
