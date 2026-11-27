-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyProjectionMass_proof_c1728933d9d0
-- name    : P2M_GroundTheory_Heights__Heights_VarietyProjectionMass_proof_c1728933d9d0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:06.72204+00:00
-- url     : https://prove2.me/theorems/0982c7b1-a8e7-59e2-a972-f17feedc35e9
-- title:
--   P2 M Ground Theory Heights  Heights Variety Projection Mass proof c1728933d9d0: P2 M Ground Theory Heights  Heights Variety Projection Mass proof c1728933d9d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Variety Projection Mass proof c1728933d9d0 construction uses the P2 M Ground Theory Heights  Heights Variety Projection Mass proof c1728933d9d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyProjectionMass.lean#L16-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyProjectionMass.lean#L16-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyProjectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphProjectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyProjectionMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MassFinite_proof_4c24bb7a8627
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NullSmaller_proof_15fa22cfb07c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_proof_0dafe800e45e

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
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_VarietyProjectionMass_proof_c1728933d9d0 (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hD : ComplexSets.DiscriminantCover.Statement) (hL : LocalGraphProjectionMass.Statement) :
    VarietyProjectionMass.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarietyProjectionMass».«proof» := P2M_GroundTheory_Heights__Heights_VarietyProjectionMass_proof_c1728933d9d0
