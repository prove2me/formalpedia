-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_proposition15
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.proposition15
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:01:03.005869+00:00
-- url     : https://prove2.me/theorems/cff97b8c-29ff-46fb-a3de-379ab27cb70f
-- title:
--   Proposition 15: full-matrix and diagonal-block linear sum rules
-- statement:
--   Let $R$ be an arbitrary unitary realization of the irreducible representation $\mu$ of $S_q$, where $q\ge1$. Let $\alpha\nearrow\mu$ denote all predecessor diagrams of size $q-1$, without a physical height restriction. Let $P_\alpha$ be the subgroup character projector and $C_\lambda$ the scalar of the sum of all transpositions in the irrep $\lambda$ (zero for an empty class). With $T_a=R((a,q))$ for $a<q$, both the full-matrix and diagonal-block sums are
--
--   $$\sum_{a<q}T_a=C_\mu I-\sum_{\alpha\nearrow\mu}C_\alpha P_\alpha,\qquad \sum_{a<q}P_\alpha T_aP_\alpha=(C_\mu-C_\alpha)P_\alpha.$$
--
--   For degree $s\ge2$, $C_\lambda=\binom{s}{2}\chi_\lambda((12))/d_\lambda$. The class-sum formulation also covers $q=1$ and an empty sum.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 18, Proposition 15: full-matrix and diagonal-block linear sum rules

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF pp.18–19 Proposition15, both full and compressed sum rules.
Class sums give the printed character coefficients whenever the class is nonempty. -/
theorem proposition15 {r D : ℕ} (mu : Schur.Partition (r+1) (r+1))
    (R : Equiv.Perm (Fin (r+1)) →* Matrix.unitaryGroup (Fin D) ℂ)
    (hR : RealizesSpechtIrrep mu R) :
    (∑ b : Fin r, (R (Equiv.swap b.castSucc (Fin.last r)) : Matrix (Fin D) (Fin D) ℂ)) =
      (classScalar mu:ℂ) • 1 - (∑ a : Preds mu,
        (classScalar a.val:ℂ) • subgroupProjector R a.val) ∧
    (∀ a : Preds mu, ∑ b : Fin r,
      subgroupProjector R a.val *
        (R (Equiv.swap b.castSucc (Fin.last r)) : Matrix (Fin D) (Fin D) ℂ) *
          subgroupProjector R a.val =
      ((classScalar mu - classScalar a.val:ℝ):ℂ) • subgroupProjector R a.val) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
