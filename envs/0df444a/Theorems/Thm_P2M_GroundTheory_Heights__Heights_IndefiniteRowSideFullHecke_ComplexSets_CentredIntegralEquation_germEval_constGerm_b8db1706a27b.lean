-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_germEval_constGerm_b8db1706a27b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_germEval_constGerm_b8db1706a27b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:21:48.429467+00:00
-- url     : https://prove2.me/theorems/496ccb31-776b-5964-a63f-7a20ca8e105a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Centred Integral Equation germ Eval const Germ b8db1706a27b: P2 M Ground Theory Heights  Heights Indefinite Row Side Ful
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Centred Integral Equation germ Eval const Germ b8db1706a27b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Centred Integral Equation germ Eval const Germ b8db1706a27b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCentredIntegralEquation.lean#L102-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCentredIntegralEquation.lean#L102-L102

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCentredIntegralEquation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
open PrimeGermPrimitivePresentation
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_germEval_constGerm_b8db1706a27b (w : σ → ℂ) (c : ℂ) : germEval w (constGerm w c) = c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«CentredIntegralEquation».«germEval_constGerm» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_germEval_constGerm_b8db1706a27b
