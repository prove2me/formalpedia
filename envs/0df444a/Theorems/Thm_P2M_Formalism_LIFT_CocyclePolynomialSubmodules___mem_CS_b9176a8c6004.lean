-- Prove2me | Theorems.Thm_P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_CS_b9176a8c6004
-- name    : P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_CS_b9176a8c6004
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:36.17997+00:00
-- url     : https://prove2.me/theorems/491f3090-7ffd-443f-b12e-91f51b667170
-- title:
--   P2 M Formalism LIFT Cocycle Polynomial Submodules   mem CS b9176a8c6004: P2 M Formalism LIFT Cocycle Polynomial Submodules   mem CS b9176a8c6004
-- statement:
--   The P2 M Formalism LIFT Cocycle Polynomial Submodules   mem CS b9176a8c6004 construction uses the P2 M Formalism LIFT Cocycle Polynomial Submodules   mem CS b9176a8c6004 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L86-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L86-L92

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

theorem P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_CS_b9176a8c6004 {ω : D} (hω : ω ∈ CS W) : W.γ ω ∈ CS W := by sorry

alias «Formalism».«LIFT».«CocyclePolynomialSubmodules».«γ_mem_CS» := P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_CS_b9176a8c6004
