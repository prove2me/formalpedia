-- Prove2me | Theorems.Thm_P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_N_4814b9af5558
-- name    : P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_N_4814b9af5558
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:50.247409+00:00
-- url     : https://prove2.me/theorems/2fd585c6-7ec1-488c-b025-5880bd2667f6
-- title:
--   P2 M Formalism LIFT Cocycle Polynomial Submodules   mem N 4814b9af5558: P2 M Formalism LIFT Cocycle Polynomial Submodules   mem N 4814b9af5558
-- statement:
--   The P2 M Formalism LIFT Cocycle Polynomial Submodules   mem N 4814b9af5558 construction uses the P2 M Formalism LIFT Cocycle Polynomial Submodules   mem N 4814b9af5558 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L71-L74

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

theorem P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_N_4814b9af5558 {n : D} (hn : n ∈ W.N) : W.γ n ∈ W.N := by sorry

alias «Formalism».«LIFT».«CocyclePolynomialSubmodules».«γ_mem_N» := P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_N_4814b9af5558
