-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_shift_eig
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.shift_eig
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:24:52.452955+00:00
-- url     : https://prove2.me/theorems/6b0bf4af-1f5d-5d38-9122-f33d70586bbf
-- title:
--   Cayley Transform Darboux: shift eig
-- statement:
--   The Cayley Transform Darboux construction uses the shift eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L65-L68

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.ThKG.CayleyTransformDarboux.shift_eig {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {H Z : A} {k : ℂ} (hk : H * Z - Z * H = k • Z) {mu : ℂ} {x : M}
    (hx : x ∈ (act H).eigenspace mu) : act Z x ∈ (act H).eigenspace (mu + k) := by sorry
