-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_main_negative
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.main_negative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:14:42.646975+00:00
-- url     : https://prove2.me/theorems/e675e929-cb59-46f9-95c7-f635d448d747
-- title:
--   Abstract main negative result, pinned to Theorem 5.1
-- statement:
--   The projective product is completed, and norm attainment means an admissible bounded absolutely convergent series with exactly optimal projective cost.
--
--   Let $R$ be an equivalent real Banach renorming of $c_0$ whose continuous bidual is strictly convex. Then there exist closed subspaces $X\subset c_0$ and $Y\subset R$ such that
--
--   $$
--   \overline{\mathrm{NA}_\pi(X\widehat\otimes_\pi Y^*)}^{\|\cdot\|_\pi}\ne X\widehat\otimes_\pi Y^*.
--   $$
--
--   These are exactly the features of Read’s space used in the proof. Equivalence of the renorming is supplied by a continuous linear equivalence with real $c_0$; approximation-property failure is a consequence used by the proof rather than an extra hypothesis on the witnesses.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 20, Abstract main negative result, pinned to Theorem 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

set_option synthInstance.maxSize 8192

namespace QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

/-- PDF pp.19–22, Theorem 5.1: uniform form for the exact features of Read's space
used by the source: an equivalent real c0 renorming with strictly convex bidual.
Both witness subspaces are closed. No approximation failure is added as a hypothesis. -/
theorem main_negative (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
    (E : CZero ℝ ℕ ≃L[ℝ] R)
    (hc : StrictlyConvex ((R →L[ℝ] ℝ) →L[ℝ] ℝ)) :
    ∃ (X : Submodule ℝ (CZero ℝ ℕ)) (Y : Submodule ℝ R),
      IsClosed (X : Set (CZero ℝ ℕ)) ∧ IsClosed (Y : Set R) ∧
      ¬ Dense {z : Projective ℝ X (Y →L[ℝ] ℝ) | TensorAttains z} := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
