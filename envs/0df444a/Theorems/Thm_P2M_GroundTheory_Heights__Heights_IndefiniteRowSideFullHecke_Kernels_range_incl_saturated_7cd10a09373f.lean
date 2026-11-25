-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_range_incl_saturated_7cd10a09373f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_range_incl_saturated_7cd10a09373f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:37:46.813955+00:00
-- url     : https://prove2.me/theorems/7217c7ad-160d-45cb-8552-1b4395b01c86
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels range incl saturated 7cd10a09373f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels range incl satu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels range incl saturated 7cd10a09373f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels range incl saturated 7cd10a09373f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RangeInclSaturated.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RangeInclSaturated.lean#L13-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RangeInclSaturated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_range_incl_saturated_7cd10a09373f {K : Type*} [Field K] [NumberField K]
    {E' E E'' : HermitianBundle K} (Y : HermitianExtension E' E E'') (t : 𝓞 K) (x : E.carrier)
    (ht : t ≠ 0) (hx : t • x ∈ LinearMap.range Y.incl) : x ∈ LinearMap.range Y.incl := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«range_incl_saturated» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_range_incl_saturated_7cd10a09373f
