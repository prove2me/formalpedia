-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_low_map
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.low_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:25.070315+00:00
-- url     : https://prove2.me/theorems/5042e497-4b68-5c32-8c95-a585edb147d6
-- title:
--   Cayley Transform Darboux: low map
-- statement:
--   The Cayley Transform Darboux construction uses the low map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L101-L106

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

theorem PositivityTheory.ThKG.CayleyTransformDarboux.low_map {M' : Type} [AddCommGroup M'] [Module ℂ M'] {T : Module.End ℂ M} {T' : Module.End ℂ M'} {lam : ℂ}
    (φ : M →ₗ[ℂ] M') (hφ : ∀ x, φ (T x) = T' (φ x)) {x : M} (hx : x ∈ low T lam) : φ x ∈ low T' lam := by sorry
