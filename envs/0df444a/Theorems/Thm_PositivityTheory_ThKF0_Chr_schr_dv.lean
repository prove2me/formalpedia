-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_schr_dv
-- name    : PositivityTheory.ThKF0.Chr.schr_dv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:51.132788+00:00
-- url     : https://prove2.me/theorems/a90962f2-adb1-4492-ba58-bcc57fad681b
-- title:
--   Chr: schr dv
-- statement:
--   The Chr construction uses the schr dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L100-L101

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}
variable [Fintype κ] [Fintype κ₁]
variable [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}

theorem PositivityTheory.ThKF0.Chr.schr_dv (w w' : V R κ) (φ₁ φ₂ : (κ → R) → ℂ) :
    schr ψ (dv w w') (boxFun φ₁ φ₂) = boxFun (schr ψ w φ₁) (schr ψ (w'.1, -w'.2) φ₂) := by sorry
