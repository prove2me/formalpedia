-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_gram_line_0ccc6c520227
-- name    : P2M_GroundTheory_Heights__Heights_KLinesLineDegree_gram_line_0ccc6c520227
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:08.771991+00:00
-- url     : https://prove2.me/theorems/72f60366-c941-467a-b194-181182a50588
-- title:
--   P2 M Ground Theory Heights  Heights KLines Line Degree gram line 0ccc6c520227: P2 M Ground Theory Heights  Heights KLines Line Degree gram line 0ccc6c520227
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Line Degree gram line 0ccc6c520227 construction uses the P2 M Ground Theory Heights  Heights KLines Line Degree gram line 0ccc6c520227 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesLineDegree.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesLineDegree.lean#L64-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Matrix
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesLineDegree
variable {K : Type} [Field K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KLinesLineDegree_gram_line_0ccc6c520227 (d : (K →+* ℂ) → Fin n → ℝ) (σ : K →+* ℂ) (x : Fin n) :
    (gramAt (diagMetric d σ) σ (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).det.re = d σ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesLineDegree».«gram_line» := P2M_GroundTheory_Heights__Heights_KLinesLineDegree_gram_line_0ccc6c520227
