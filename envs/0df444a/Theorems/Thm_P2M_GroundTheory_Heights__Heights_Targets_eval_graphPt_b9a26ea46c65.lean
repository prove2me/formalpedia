-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_eval_graphPt_b9a26ea46c65
-- name    : P2M_GroundTheory_Heights__Heights_Targets_eval_graphPt_b9a26ea46c65
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:33.438806+00:00
-- url     : https://prove2.me/theorems/46ed04e4-679c-45b6-b4bf-22734d128dbd
-- title:
--   P2 M Ground Theory Heights  Heights Targets eval graph Pt b9a26ea46c65: P2 M Ground Theory Heights  Heights Targets eval graph Pt b9a26ea46c65
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets eval graph Pt b9a26ea46c65 construction uses the P2 M Ground Theory Heights  Heights Targets eval graph Pt b9a26ea46c65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L40-L51

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

theorem P2M_GroundTheory_Heights__Heights_Targets_eval_graphPt_b9a26ea46c65 (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (q : MvPolynomial (Fin (n + 1)) ℂ) :
    eval (graphPt p x) q = eval x (graphHom p q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«eval_graphPt» := P2M_GroundTheory_Heights__Heights_Targets_eval_graphPt_b9a26ea46c65
