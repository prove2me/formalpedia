-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_un_mem
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.un_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:24:45.810728+00:00
-- url     : https://prove2.me/theorems/b440b3c4-79b9-59d4-b90e-3dbf623ec51b
-- title:
--   Cayley Transform Darboux: un mem
-- statement:
--   The Cayley Transform Darboux construction uses the un mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L136-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L136-L144

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

theorem PositivityTheory.ThKG.CayleyTransformDarboux.un_mem {r : I → I → Prop} (w : ι) {a b : I} (h : r a b) : un w a b ∈ alg ι r := by sorry
