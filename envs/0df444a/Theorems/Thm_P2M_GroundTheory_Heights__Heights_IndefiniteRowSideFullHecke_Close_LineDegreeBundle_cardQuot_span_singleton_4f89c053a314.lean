-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_cardQuot_span_singleton_4f89c053a314
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_cardQuot_span_singleton_4f89c053a314
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:05.852907+00:00
-- url     : https://prove2.me/theorems/09b0fb7c-abb9-4363-a597-76d3d8eb7bdf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle card Quot span singleton 4f89c053a314: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Cl
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle card Quot span singleton 4f89c053a314 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle card Quot span singleton 4f89c053a314 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineDegreeBundle.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineDegreeBundle.lean#L33-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LineDegreeBundleStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLineDegreeBundle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder nonZeroDivisors
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_cardQuot_span_singleton_4f89c053a314 {L : Type*} [Field L] [NumberField L] (a : 𝓞 L) :
    (Submodule.cardQuot (Ideal.span {a} : Ideal (𝓞 L)) : ℝ) = |(Algebra.norm ℚ (a : L) : ℝ)| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«LineDegreeBundle».«cardQuot_span_singleton» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_cardQuot_span_singleton_4f89c053a314
