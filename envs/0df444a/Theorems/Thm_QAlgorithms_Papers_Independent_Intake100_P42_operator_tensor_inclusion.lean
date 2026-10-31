-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P42_operator_tensor_inclusion
-- name    : QAlgorithms.Papers.Independent.Intake100.P42.operator_tensor_inclusion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:23:06.984811+00:00
-- url     : https://prove2.me/theorems/b84a1eae-35d2-4745-a4a5-131da97982d2
-- title:
--   Canonical bounded realization of algebraic operator tensors
-- statement:
--   Fix a uniform crossnorm family $\alpha$ over $\mathbb F=\mathbb R$ or $\mathbb C$, and arbitrary normed spaces $X,Y,V,W$. The canonical linear action $J$ of the algebraic operator tensor product is injective and bounded on every operator tensor:
--
--   $$J:\mathcal B(X,V)\otimes\mathcal B(Y,W)\hookrightarrow\mathcal B(X\otimes_\alpha Y,V\otimes_\alpha W),\qquad J(A\otimes B)(x\otimes y)=Ax\otimes By.$$
--
--   The pullback $L\mapsto\|J(L)\|$ is a genuine norm. Thus the same canonical realization gives the stated inclusion when the operator tensor product is equipped with this induced norm. The construction does not depend on a chosen finite-sum representation. The underlying tensor spaces are algebraic, and all factors may be incomplete or zero.
-- source:
--   Restriction of Uniform Crossnorms, arXiv:2212.10780v2, PDF p. 4, Proposition 3.1: canonical inclusion of algebraic bounded-map tensors

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P42

open scoped TensorProduct ENNReal

open QAlgorithms.Papers.Independent.Next46.P02

universe u

variable {F : Type u} [RCLike F]

/-- PDF p.4, Proposition 3.1: canonical injective bounded realization of
ALL finite operator tensors, with the genuine transported norm. Boundedness
is a conclusion and no chosen tensor representation is part of the input. -/
theorem operator_tensor_inclusion (a : CrossnormFamily F) (ha : IsUniform a)
    (X Y V W : Type u)
    [NormedAddCommGroup X] [NormedSpace F X]
    [NormedAddCommGroup Y] [NormedSpace F Y]
    [NormedAddCommGroup V] [NormedSpace F V]
    [NormedAddCommGroup W] [NormedSpace F W] :
    Function.Injective (operatorAction (F := F) (X := X) (Y := Y) (V := V) (W := W)) ∧
    (∀ L : TensorProduct F (X →L[F] V) (Y →L[F] W),
      BoundedIn (a.norm X Y) (a.norm V W) (operatorAction L) ∧
      extendedOperatorNorm (a.norm X Y) (a.norm V W) (operatorAction L) < ⊤) ∧
    NormOn (F := F) (fun _ => True) (restrictedOperatorNorm (a.norm X Y) (a.norm V W)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P42

end
