-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_tensorActionsGiveModules
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.tensorActionsGiveModules
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:30:42.725477+00:00
-- url     : https://prove2.me/theorems/257b04c9-960f-4379-bd47-7f82d8a1b2c4
-- title:
--   Tensor actions give left modules
-- statement:
--   Let $(M,m,e)$ be a tensor monoid in abelian groups, and give $M$ the ring structure with $xy=m(x\otimes y)$ and $1=e(1)$. Let $A$ be an abelian group and $n:M\otimes_{\mathbb Z}A\to A$ a $\mathbb Z$-linear map satisfying the monoidal unit and action associativity diagrams. There is a left $M$-module structure on the same additive group $A$, with
--
--   $$r\cdot a=n(r\otimes a).$$
--
--   The unit and associativity requirements are $n(e(1)\otimes a)=a$ and $n(m(r\otimes s)\otimes a)=n(r\otimes n(s\otimes a))$. Tensor linearity supplies additivity in each argument, so both distributivity laws belong to the resulting module. This uses the ring constructed from the given monoid.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 5, §1, Group Actions

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF p. 5: a tensor action makes the SAME abelian group a left module
 over the ring computed from the given monoid. Scalar multiplication is the
 given tensor map on pure tensors, so neither distributivity can be dropped. -/
theorem tensorActionsGiveModules (M : ModuleCat.{0} ℤ) [MonObj M]
    (A : Type v) [AddCommGroup A] (n : TensorProduct ℤ M A →ₗ[ℤ] A)
    (h : TensorActionDiagrams M A n) :
    letI : Ring M := tensorRing M
    ∃ a : Module M A, ∀ r x, @SMul.smul M A a.toSMul r x = n (r ⊗ₜ[ℤ] x) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
