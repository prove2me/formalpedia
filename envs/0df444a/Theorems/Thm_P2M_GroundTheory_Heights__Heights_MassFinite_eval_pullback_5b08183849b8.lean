-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MassFinite_eval_pullback_5b08183849b8
-- name    : P2M_GroundTheory_Heights__Heights_MassFinite_eval_pullback_5b08183849b8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:55.340824+00:00
-- url     : https://prove2.me/theorems/296c651c-699c-4d5d-a15f-78c1ce5df020
-- title:
--   P2 M Ground Theory Heights  Heights Mass Finite eval pullback 5b08183849b8: P2 M Ground Theory Heights  Heights Mass Finite eval pullback 5b08183849b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Mass Finite eval pullback 5b08183849b8 construction uses the P2 M Ground Theory Heights  Heights Mass Finite eval pullback 5b08183849b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFinite.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFinite.lean#L35-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite
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
open GroundTheory.Heights₂.Heights.MassFinite

theorem P2M_GroundTheory_Heights__Heights_MassFinite_eval_pullback_5b08183849b8 {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (P : MvPolynomial (Fin d) ℂ)
    (x : Fin n → ℂ) : eval x (ComplexSets.pullback A P) = eval (A *ᵥ x) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MassFinite».«eval_pullback» := P2M_GroundTheory_Heights__Heights_MassFinite_eval_pullback_5b08183849b8
