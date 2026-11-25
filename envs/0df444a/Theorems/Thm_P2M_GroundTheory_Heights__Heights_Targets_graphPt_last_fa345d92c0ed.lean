-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphPt_last_fa345d92c0ed
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphPt_last_fa345d92c0ed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:40:24.687576+00:00
-- url     : https://prove2.me/theorems/3f2b9ecf-d796-41e1-bb4b-e973b81dedcb
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Pt last fa345d92c0ed: P2 M Ground Theory Heights  Heights Targets graph Pt last fa345d92c0ed
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Pt last fa345d92c0ed construction uses the P2 M Ground Theory Heights  Heights Targets graph Pt last fa345d92c0ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L56-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_graphPt_last_fa345d92c0ed (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : graphPt p x (Fin.last n) = eval x p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphPt_last» := P2M_GroundTheory_Heights__Heights_Targets_graphPt_last_fa345d92c0ed
