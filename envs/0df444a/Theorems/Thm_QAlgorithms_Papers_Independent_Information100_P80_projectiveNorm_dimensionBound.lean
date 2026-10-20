-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P80_projectiveNorm_dimensionBound
-- name    : QAlgorithms.Papers.Independent.Information100.P80.projectiveNorm_dimensionBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:16:29.739419+00:00
-- url     : https://prove2.me/theorems/b7dab9c3-217a-462d-be90-6a374bbcda36
-- title:
--   Lemma 2 (Dimension bound for the projective tensor norm)
-- statement:
--   Let $B$ and $E$ be positive finite-dimensional registers. For an arbitrary complex operator $Z$ on $B\otimes E$, define its projective norm by
--   $$
--   \|Z\|_\pi=\inf_{Z=\sum_jX_j\otimes Y_j}\sum_j\|X_j\|_\infty\|Y_j\|_\infty,
--   $$
--   where the infimum ranges over all finite exact decompositions and each local norm is the spectral norm. Then
--   $$
--   \|Z\|_\pi\le\min\{(\dim B)^2,(\dim E)^2\}\,\|Z\|_\infty.
--   $$
--
--   No Hermiticity or positivity is assumed. This relates the cost of a bipartite operator decomposition to local dimensions and the global spectral norm.
-- source:
--   Strong Converses for Quantum Channel Capacities from Blowing-Up Lemmata, arXiv:2609.11771v1, PDF p. 6, Lemma 2 (Dimension bound for the projective tensor norm)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P80

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

/-- Lemma 2, PDF p.6, (18): the projective norm uses local spectral norms. -/
theorem projectiveNorm_dimensionBound
    {B E : Type*} [Fintype B] [Fintype E] [DecidableEq B] [DecidableEq E]
    [Nonempty B] [Nonempty E] (Z : Matrix (B × E) (B × E) ℂ) :
    projectiveNorm Z ≤
      (min ((Fintype.card B : ℝ) ^ 2) ((Fintype.card E : ℝ) ^ 2)) * specNorm Z := by sorry

end QAlgorithms.Papers.Independent.Information100.P80

end
