-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_rel_dv
-- name    : PositivityTheory.ThKF0.Chr.rel_dv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:19.813165+00:00
-- url     : https://prove2.me/theorems/1d2af707-dba4-4c74-ae91-d95ee16c5bc2
-- title:
--   Chr: rel dv
-- statement:
--   The Chr construction uses the rel dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L29-L45

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

theorem PositivityTheory.ThKF0.Chr.rel_dv {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} (hj : Function.Injective j) {w w' : V R κ} {w₁ w₁' : V R κ₁} :
    Rel (dbS S) (Sum.map j j) (dv w w') (dv w₁ w₁') ↔ Rel S j w w₁ ∧ Rel S j w' w₁' := by sorry
