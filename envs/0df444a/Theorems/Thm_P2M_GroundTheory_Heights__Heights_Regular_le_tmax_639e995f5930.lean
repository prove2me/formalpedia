-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_le_tmax_639e995f5930
-- name    : P2M_GroundTheory_Heights__Heights_Regular_le_tmax_639e995f5930
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:01.292672+00:00
-- url     : https://prove2.me/theorems/fb326856-c61c-4468-9550-ab2f97bc7971
-- title:
--   P2 M Ground Theory Heights  Heights Regular le tmax 639e995f5930: P2 M Ground Theory Heights  Heights Regular le tmax 639e995f5930
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular le tmax 639e995f5930 construction uses the P2 M Ground Theory Heights  Heights Regular le tmax 639e995f5930 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L22-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
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
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_le_tmax_639e995f5930 {ι : Type*} [Fintype ι] [Nonempty ι] (t : ι → ℝ) (i : ι) : t i ≤ tmax t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«le_tmax» := P2M_GroundTheory_Heights__Heights_Regular_le_tmax_639e995f5930
