-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_tensorMonoidsGiveRings
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.tensorMonoidsGiveRings
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:29:57.150928+00:00
-- url     : https://prove2.me/theorems/4e877566-5554-4633-8551-ab8261a983e8
-- title:
--   Tensor monoid objects in Ab give rings
-- statement:
--   View an abelian group $M$ as its canonical $\mathbb Z$-module. Suppose $m:M\otimes_{\mathbb Z}M\to M$ and $e:\mathbb Z\to M$ form a monoid object for the tensor monoidal structure, with its associator and unitors. There is a ring structure with the original additive group and
--
--   $$1_M=e(1),\qquad xy=m(x\otimes y).$$
--
--   It is the ring computed by Mathlib's tensor-monoid construction. Multiplication need not be commutative, and the zero ring is permitted. As footnote 5 explains, $\mathbb Z$ is the tensor unit, rather than a terminal object of Ab.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 5, §1, Group Actions and footnote 5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF p. 5: a tensor monoid in Ab gives a ring with its original addition,
unit e(1), and multiplication m(x tensor y). The zero ring is allowed. -/
theorem tensorMonoidsGiveRings (M : ModuleCat.{0} ℤ) [MonObj M] :
    let originalAddition : AddCommGroup M := inferInstance
    let tensorMultiplication : M → M → M :=
      fun x y => MonObj.mul (X := M) (x ⊗ₜ[ℤ] y)
    ∃ r : Ring M,
      r = tensorRing M ∧ r.toAddCommGroup = originalAddition ∧
      r.one = MonObj.one (X := M) (1 : ℤ) ∧
      (∀ x y : M, r.mul x y = tensorMultiplication x y) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
