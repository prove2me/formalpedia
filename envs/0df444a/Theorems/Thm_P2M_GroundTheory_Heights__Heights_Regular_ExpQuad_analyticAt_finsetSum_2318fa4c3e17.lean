-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_finsetSum_2318fa4c3e17
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_finsetSum_2318fa4c3e17
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:09.352728+00:00
-- url     : https://prove2.me/theorems/fc262519-dbf2-42d4-b69f-6f2d3325b620
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad analytic At finset Sum 2318fa4c3e17: P2 M Ground Theory Heights  Heights Regular Exp Quad analytic At finset Sum 2318fa4c3e17
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad analytic At finset Sum 2318fa4c3e17 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad analytic At finset Sum 2318fa4c3e17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L67-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_finsetSum_2318fa4c3e17 {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → (Fin n → ℂ) → ℂ}
    {w : Fin n → ℂ} (h : ∀ i ∈ s, AnalyticAt ℂ (f i) w) :
    AnalyticAt ℂ (fun x => ∑ i ∈ s, f i x) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«analyticAt_finsetSum» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_finsetSum_2318fa4c3e17
