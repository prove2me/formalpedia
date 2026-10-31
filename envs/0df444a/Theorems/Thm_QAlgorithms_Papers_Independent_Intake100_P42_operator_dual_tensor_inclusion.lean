-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P42_operator_dual_tensor_inclusion
-- name    : QAlgorithms.Papers.Independent.Intake100.P42.operator_dual_tensor_inclusion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:23:41.514713+00:00
-- url     : https://prove2.me/theorems/13d37c12-e4c0-4cac-80f4-87aa6f90cac9
-- title:
--   Product operator-duals embed continuously with the product norm bound
-- statement:
--   Fix a uniform crossnorm family $\alpha$ and arbitrary normed spaces $X,Y,V,W$ over the common real or complex field $\mathbb F$. Set $E=\mathcal B(X,V)$, $G=\mathcal B(Y,W)$, and equip $E\otimes G$ with its canonical induced norm $\rho_\alpha$. Every algebraic tensor of the full continuous duals $E^*\otimes G^*$ defines a continuous linear functional on this space, and this canonical algebraic realization is injective. For every $\phi\in E^*$ and $\eta\in G^*$,
--
--   $$\|\phi\otimes\eta\|_{\rho_\alpha^*}\le\|\phi\|\,\|\eta\|,\qquad |(\phi\otimes\eta)(L)|\le\|\phi\|\,\|\eta\|\,\rho_\alpha(L).$$
--
--   The scalar pairing is bilinear: $(\phi\otimes\eta)(A\otimes B)=\phi(A)\eta(B)$. Every finite sum has finite dual norm, giving the continuous-dual inclusion with its pulled-back norm. No continuity or desired dual bound is assumed for these tensors.
-- source:
--   Restriction of Uniform Crossnorms, arXiv:2212.10780v2, PDF p. 4, Proposition 3.2: product operator-dual functionals and continuous dual inclusion

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P42

open scoped TensorProduct ENNReal

open QAlgorithms.Papers.Independent.Next46.P02

universe u

variable {F : Type u} [RCLike F]

/-- PDF pp.4--5, Proposition 3.2: algebraic dual inclusion, product dual norm
bound, and bounded realization of every finite dual tensor. Both injections
use the full continuous duals of the original bounded-map factors. -/
theorem operator_dual_tensor_inclusion (a : CrossnormFamily F) (ha : IsUniform a)
    (X Y V W : Type u)
    [NormedAddCommGroup X] [NormedSpace F X]
    [NormedAddCommGroup Y] [NormedSpace F Y]
    [NormedAddCommGroup V] [NormedSpace F V]
    [NormedAddCommGroup W] [NormedSpace F W] :
    let r := restrictedOperatorNorm (a.norm X Y) (a.norm V W)
    Function.Injective
      (dualTensorPairing (F := F) (X := X →L[F] V) (Y := Y →L[F] W)) ∧
    (∀ k : TensorProduct F ((X →L[F] V) →L[F] F) ((Y →L[F] W) →L[F] F),
      BoundedIn r (fun z : F => ‖z‖) (dualTensorPairing k) ∧
      extendedOperatorNorm r (fun z : F => ‖z‖) (dualTensorPairing k) < ⊤) ∧
    (∀ (f : (X →L[F] V) →L[F] F) (g : (Y →L[F] W) →L[F] F),
      algebraicMapNorm r (fun z : F => ‖z‖) (banachTensorEval f g) ≤ ‖f‖ * ‖g‖ ∧
      ∀ L, ‖banachTensorEval f g L‖ ≤ ‖f‖ * ‖g‖ * r L) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P42

end
