-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_shift_low
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.shift_low
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:31:41.1464+00:00
-- url     : https://prove2.me/theorems/7a620f13-e314-4d47-91b1-2577e08acb03
-- title:
--   Cayley Transform Darboux: shift low
-- statement:
--   The Cayley Transform Darboux construction uses the shift low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L70-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L70-L82

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

theorem PositivityTheory.ThKG.CayleyTransformDarboux.shift_low {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {H Z : A} {k : ℝ} (h0 : 0 < k)
    (hk : H * Z - Z * H = (-(k : ℂ)) • Z) {lam : ℂ} {V : Submodule ℂ M} (hV : V ≤ (act H).eigenspace lam) :
    ∀ x ∈ V ⊔ low (act H) lam, act Z x ∈ V ⊔ low (act H) lam := by sorry
