-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_exists_form
-- name    : PositivityTheory.ThKF0.Chr.Ax.exists_form
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:04:01.866778+00:00
-- url     : https://prove2.me/theorems/9fe4b447-ea63-555c-9ca5-89c3d255a263
-- title:
--   Ax: exists form
-- statement:
--   The Ax construction uses the exists form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L113-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L113-L118

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
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
variable {R : Type} [CommRing R] [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
  {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]

theorem PositivityTheory.ThKF0.Chr.Ax.exists_form (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) : ∃ l ∈ C.adm κ,
    (∀ w, (S w).1 = 0 → ∀ φ ∈ C.sp κ, l (schr ψ w φ) = l φ) ∧ Cyc C ψ l := by sorry
