-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_aeval_mem_adjoin_ddb610f1d1e5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_aeval_mem_adjoin_ddb610f1d1e5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:25.397831+00:00
-- url     : https://prove2.me/theorems/7c15c709-d20f-4a1e-a635-f9297df064dd
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fibre Transcendence aeval mem adjoin ddb610f1d1e5: P2 M Ground Theory Heights  Heights Inter Fibre Transcendence aeval mem adjoin ddb610f1d1e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fibre Transcendence aeval mem adjoin ddb610f1d1e5 construction uses the P2 M Ground Theory Heights  Heights Inter Fibre Transcendence aeval mem adjoin ddb610f1d1e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AevalMemAdjoin.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AevalMemAdjoin.lean#L23-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsEvalKerKrullDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AevalMemAdjoin
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.FibreTranscendence

theorem P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_aeval_mem_adjoin_ddb610f1d1e5 {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] {J : Type} (y : J → L)
    (g : MvPolynomial J ℤ) : aeval y g ∈ IntermediateField.adjoin (ZMod p) (Set.range y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FibreTranscendence».«aeval_mem_adjoin» := P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_aeval_mem_adjoin_ddb610f1d1e5
