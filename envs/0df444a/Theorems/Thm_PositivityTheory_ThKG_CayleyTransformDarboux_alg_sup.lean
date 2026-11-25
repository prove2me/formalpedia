-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_alg_sup
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.alg_sup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:36.469363+00:00
-- url     : https://prove2.me/theorems/a2745af5-56b0-5dff-85f3-e2d44645b18b
-- title:
--   Cayley Transform Darboux: alg sup
-- statement:
--   The Cayley Transform Darboux construction uses the alg sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L159-L161

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

theorem PositivityTheory.ThKG.CayleyTransformDarboux.alg_sup {r r₁ r₂ : I → I → Prop} (h : ∀ a b, r a b → r₁ a b ∨ r₂ a b) : alg ι r ≤ alg ι r₁ ⊔ alg ι r₂ := by sorry
