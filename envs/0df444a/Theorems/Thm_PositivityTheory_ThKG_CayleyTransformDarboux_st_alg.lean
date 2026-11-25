-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_st_alg
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.st_alg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:28:19.082112+00:00
-- url     : https://prove2.me/theorems/48fd6fa4-4993-59e8-a204-cff0a6a7fd8b
-- title:
--   Cayley Transform Darboux: st alg
-- statement:
--   The Cayley Transform Darboux construction uses the st alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L169-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L169-L171

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

theorem PositivityTheory.ThKG.CayleyTransformDarboux.st_alg {act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M} {r : I → I → Prop} {N : Submodule ℂ M}
    (h : ∀ w a b, r a b → ∀ x ∈ N, act (un w a b) x ∈ N) : St act (alg ι r) N := by sorry
