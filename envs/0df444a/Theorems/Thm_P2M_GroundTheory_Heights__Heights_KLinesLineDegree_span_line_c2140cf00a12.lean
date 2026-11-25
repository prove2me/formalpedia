-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_span_line_c2140cf00a12
-- name    : P2M_GroundTheory_Heights__Heights_KLinesLineDegree_span_line_c2140cf00a12
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:12.732805+00:00
-- url     : https://prove2.me/theorems/1d45ee01-1bcf-4268-a672-bfb82f21b299
-- title:
--   P2 M Ground Theory Heights  Heights KLines Line Degree span line c2140cf00a12: P2 M Ground Theory Heights  Heights KLines Line Degree span line c2140cf00a12
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Line Degree span line c2140cf00a12 construction uses the P2 M Ground Theory Heights  Heights KLines Line Degree span line c2140cf00a12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesLineDegree.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesLineDegree.lean#L52-L62

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

theorem P2M_GroundTheory_Heights__Heights_KLinesLineDegree_span_line_c2140cf00a12 (x : Fin n) :
    (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).toAddSubgroup =
      ((1 : Submodule (𝓞 K) K).toAddSubgroup).map (AddMonoidHom.single (fun _ : Fin n => K) x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesLineDegree».«span_line» := P2M_GroundTheory_Heights__Heights_KLinesLineDegree_span_line_c2140cf00a12
