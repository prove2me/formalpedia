-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_alg_le
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.alg_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:18.211369+00:00
-- url     : https://prove2.me/theorems/94339ff2-b7e2-41f6-b3d7-77122c5b7648
-- title:
--   Cayley Transform Darboux: alg le
-- statement:
--   The Cayley Transform Darboux construction uses the alg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L128-L134

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
variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.ThKG.CayleyTransformDarboux.alg_le {r : I → I → Prop} {S : Submodule ℂ (ι → Matrix I I ℂ)} (h : ∀ w a b, r a b → un w a b ∈ S) : alg ι r ≤ S := by sorry
