-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_density_distinction
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.density_distinction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:07:43.459824+00:00
-- url     : https://prove2.me/theorems/ec5b7ee3-c6bd-454d-bb9a-d0a33a17fe76
-- title:
--   Remark 3.13: norm-density distinction and weak-star density
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Attaining tensors are dense in $L_1[0,1]\widehat\otimes_\pi L_1[0,1]$, but classical norm-attaining bilinear forms are not norm dense for those factors. For arbitrary Banach $X\ne0,Y$, tensor norm density still implies
--
--   $$
--   \overline{\mathrm{NA}(X,Y^*)\cap B_{\mathcal L(X,Y^*)}}^{\,w^*}=B_{\mathcal L(X,Y^*)}.
--   $$
--
--   The weak-star topology is that of the full projective predual $P(X,Y)$. The printed reference to Example 3.12(c) is corrected to (d); both clauses of the remark are retained.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 11, Remark 3.13: norm-density distinction and weak-star density

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

/-- PDF p.11, Remark 3.13: tensor density does not imply bilinear norm density, but
classically attaining operators in the unit ball are weak-star dense in the operator ball.
The printed reference 3.12(c) is corrected to 3.12(d), the actual L1 example.
The printed universal clause does not exclude X=0; nonzero X is required because
its classical attaining set and weak-star closure would otherwise be empty. -/
theorem density_distinction :
    (TensorDense K (IntervalL1 K) (IntervalL1 K) ∧
      ¬ Dense {B : Bilinear K (IntervalL1 K) (IntervalL1 K) K | BilinearAttains B}) ∧
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
      [Nontrivial X] [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y],
      TensorDense K X Y → ∀ T : X →L[K] (Y →L[K] K), ‖T‖ ≤ 1 →
        InTensorWeakStarClosure {S | OperatorAttains S ∧ ‖S‖ ≤ 1} T) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
