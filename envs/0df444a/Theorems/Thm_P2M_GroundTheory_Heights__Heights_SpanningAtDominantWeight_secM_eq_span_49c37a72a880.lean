-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_secM_eq_span_49c37a72a880
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_secM_eq_span_49c37a72a880
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:24.850444+00:00
-- url     : https://prove2.me/theorems/b25999ca-b6bc-430d-bf44-f1bf57a2c4d9
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight sec M eq span 49c37a72a880: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight sec M eq span 49c37a72a880
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight sec M eq span 49c37a72a880 construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight sec M eq span 49c37a72a880 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L86-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L86-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_secM_eq_span_49c37a72a880 {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) :
    Geo.secM (ι := blockIdx n) y d = (Submodule.span ℤ (monomialValues y d)).toAddSubgroup := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«secM_eq_span» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_secM_eq_span_49c37a72a880
