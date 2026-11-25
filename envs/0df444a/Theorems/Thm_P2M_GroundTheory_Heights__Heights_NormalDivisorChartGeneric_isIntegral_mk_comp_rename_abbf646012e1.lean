-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDivisorChartGeneric_isIntegral_mk_comp_rename_abbf646012e1
-- name    : P2M_GroundTheory_Heights__Heights_NormalDivisorChartGeneric_isIntegral_mk_comp_rename_abbf646012e1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:04:55.235424+00:00
-- url     : https://prove2.me/theorems/5c64994e-65c0-5629-abad-18f5820150f8
-- title:
--   P2 M Ground Theory Heights  Heights Normal Divisor Chart Generic is Integral mk comp rename abbf646012e1: P2 M Ground Theory Heights  Heights Normal Divisor Chart Generic is Integral mk comp rename ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Divisor Chart Generic is Integral mk comp rename abbf646012e1 construction uses the P2 M Ground Theory Heights  Heights Normal Divisor Chart Generic is Integral mk comp rename abbf646012e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDivisorChartGeneric.lean#L29-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDivisorChartGeneric.lean#L29-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDivisorChartGeneric
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDivisorChartGeneric

theorem P2M_GroundTheory_Heights__Heights_NormalDivisorChartGeneric_isIntegral_mk_comp_rename_abbf646012e1 {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) {B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)} (hB : M.ideal ≤ B) :
    ((Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom).IsIntegral := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalDivisorChartGeneric».«isIntegral_mk_comp_rename» := P2M_GroundTheory_Heights__Heights_NormalDivisorChartGeneric_isIntegral_mk_comp_rename_abbf646012e1
