-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_aeval_red_da59eedff835
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_aeval_red_da59eedff835
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:14.355004+00:00
-- url     : https://prove2.me/theorems/adbb9460-327c-4c0a-9765-7c6631a33f9a
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fibre Transcendence aeval red da59eedff835: P2 M Ground Theory Heights  Heights Inter Fibre Transcendence aeval red da59eedff835
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fibre Transcendence aeval red da59eedff835 construction uses the P2 M Ground Theory Heights  Heights Inter Fibre Transcendence aeval red da59eedff835 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AevalMemAdjoin.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AevalMemAdjoin.lean#L15-L21

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

theorem P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_aeval_red_da59eedff835 {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] {J : Type} (y : J → L)
    (g : MvPolynomial J ℤ) :
    aeval y (MvPolynomial.map (Int.castRingHom (ZMod p)) g) = aeval y g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FibreTranscendence».«aeval_red» := P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_aeval_red_da59eedff835
