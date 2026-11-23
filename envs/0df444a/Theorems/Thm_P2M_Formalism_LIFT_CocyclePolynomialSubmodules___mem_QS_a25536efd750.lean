-- Prove2me | Theorems.Thm_P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_QS_a25536efd750
-- name    : P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_QS_a25536efd750
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:52.938318+00:00
-- url     : https://prove2.me/theorems/69b22256-870d-4edf-80cd-1f4899494636
-- title:
--   P2 M Formalism LIFT Cocycle Polynomial Submodules   mem QS a25536efd750: P2 M Formalism LIFT Cocycle Polynomial Submodules   mem QS a25536efd750
-- statement:
--   The P2 M Formalism LIFT Cocycle Polynomial Submodules   mem QS a25536efd750 construction uses the P2 M Formalism LIFT Cocycle Polynomial Submodules   mem QS a25536efd750 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L76-L84

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Formalism.LIFT.CocyclePolynomialSubmodules
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)

theorem P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_QS_a25536efd750 {y : D} (hy : y ∈ QS W) : W.γ y ∈ QS W := by sorry

alias «Formalism».«LIFT».«CocyclePolynomialSubmodules».«γ_mem_QS» := P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_QS_a25536efd750
