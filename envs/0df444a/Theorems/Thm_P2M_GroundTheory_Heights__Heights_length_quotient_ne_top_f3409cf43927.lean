-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_quotient_ne_top_f3409cf43927
-- name    : P2M_GroundTheory_Heights__Heights_length_quotient_ne_top_f3409cf43927
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:52.71483+00:00
-- url     : https://prove2.me/theorems/c619633a-76aa-44cb-b0d4-eb2b3c6bb2cc
-- title:
--   P2 M Ground Theory Heights  Heights length quotient ne top f3409cf43927: P2 M Ground Theory Heights  Heights length quotient ne top f3409cf43927
-- statement:
--   The P2 M Ground Theory Heights  Heights length quotient ne top f3409cf43927 construction uses the P2 M Ground Theory Heights  Heights length quotient ne top f3409cf43927 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveNormalisationLength.lean#L36-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveNormalisationLength.lean#L36-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StExtensionQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveNormalisationLength
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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_length_quotient_ne_top_f3409cf43927 {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (hdim : ringKrullDim O = 1) {x : O} (hx : x ∈ nonZeroDivisors O) :
    Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«length_quotient_ne_top» := P2M_GroundTheory_Heights__Heights_length_quotient_ne_top_f3409cf43927
