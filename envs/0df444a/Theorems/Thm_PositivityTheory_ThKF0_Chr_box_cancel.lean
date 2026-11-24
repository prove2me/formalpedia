-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_box_cancel
-- name    : PositivityTheory.ThKF0.Chr.box_cancel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:15.934173+00:00
-- url     : https://prove2.me/theorems/1f7e37b9-2a87-43f2-bca8-bac87014c331
-- title:
--   Chr: box cancel
-- statement:
--   The Chr construction uses the box cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L110-L112

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
omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁]

theorem PositivityTheory.ThKF0.Chr.box_cancel {φ₁ φ₁' : (κ → R) → ℂ} {φ₂ : (κ₁ → R) → ℂ} (h₂ : φ₂ ≠ 0) (h : boxFun φ₁ φ₂ = boxFun φ₁' φ₂) : φ₁ = φ₁' := by sorry
