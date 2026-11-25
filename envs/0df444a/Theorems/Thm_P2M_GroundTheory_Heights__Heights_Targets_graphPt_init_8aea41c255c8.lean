-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphPt_init_8aea41c255c8
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphPt_init_8aea41c255c8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:40:24.690266+00:00
-- url     : https://prove2.me/theorems/3bd99c4c-2a73-49e9-9a8c-1573b0374c49
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Pt init 8aea41c255c8: P2 M Ground Theory Heights  Heights Targets graph Pt init 8aea41c255c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Pt init 8aea41c255c8 construction uses the P2 M Ground Theory Heights  Heights Targets graph Pt init 8aea41c255c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L53-L54

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

theorem P2M_GroundTheory_Heights__Heights_Targets_graphPt_init_8aea41c255c8 (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin.init (graphPt p x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphPt_init» := P2M_GroundTheory_Heights__Heights_Targets_graphPt_init_8aea41c255c8
