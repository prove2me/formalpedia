-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_low_eig
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.low_eig
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:24:29.839661+00:00
-- url     : https://prove2.me/theorems/d756f217-14da-592c-82a7-199bf88a5faa
-- title:
--   Cayley Transform Darboux: low eig
-- statement:
--   The Cayley Transform Darboux construction uses the low eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L92-L99

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

theorem PositivityTheory.ThKG.CayleyTransformDarboux.low_eig {T : Module.End ℂ M} {lam : ℂ} {x : M} (h1 : x ∈ low T lam) (h2 : x ∈ T.eigenspace lam) : x = 0 := by sorry
