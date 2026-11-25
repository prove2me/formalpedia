-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_schr_box
-- name    : PositivityTheory.ThKF0.Chr.schr_box
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:04:18.328846+00:00
-- url     : https://prove2.me/theorems/d49a9359-98d0-5651-9068-0a0df76bbda6
-- title:
--   Chr: schr box
-- statement:
--   The Chr construction uses the schr box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L91-L98

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

theorem PositivityTheory.ThKF0.Chr.schr_box {κ' : Type} [Fintype κ'] (w : V R κ) (w' : V R κ') (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ (Sum.elim w.1 w'.1, Sum.elim w.2 w'.2) (boxFun φ₁ φ₂) = boxFun (schr ψ w φ₁) (schr ψ w' φ₂) := by sorry
