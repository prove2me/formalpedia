-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CentredRingNormal_mem_valuationSubring_iff_place_091f0caf95c7
-- name    : P2M_GroundTheory_Heights__Heights_CentredRingNormal_mem_valuationSubring_iff_place_091f0caf95c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:20.874741+00:00
-- url     : https://prove2.me/theorems/4ee50f74-41aa-4858-b978-0a6cdf705bd8
-- title:
--   P2 M Ground Theory Heights  Heights Centred Ring Normal mem valuation Subring iff place 091f0caf95c7: P2 M Ground Theory Heights  Heights Centred Ring Normal mem valuation Subring iff place 091f0caf95
-- statement:
--   The P2 M Ground Theory Heights  Heights Centred Ring Normal mem valuation Subring iff place 091f0caf95c7 construction uses the P2 M Ground Theory Heights  Heights Centred Ring Normal mem valuation Subring iff place 091f0caf95c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PCentredRingNormal.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PCentredRingNormal.lean#L22-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PCentredRingNormal
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
open NumberField IsDedekindDomain
open GroundTheory.Heights₂.Heights.CentredRingNormal
variable {L : Type} [Field L] [NumberField L]

theorem P2M_GroundTheory_Heights__Heights_CentredRingNormal_mem_valuationSubring_iff_place_091f0caf95c7 (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    x ∈ (v.valuation L).valuationSubring ↔ FinitePlace.mk v x ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CentredRingNormal».«mem_valuationSubring_iff_place» := P2M_GroundTheory_Heights__Heights_CentredRingNormal_mem_valuationSubring_iff_place_091f0caf95c7
