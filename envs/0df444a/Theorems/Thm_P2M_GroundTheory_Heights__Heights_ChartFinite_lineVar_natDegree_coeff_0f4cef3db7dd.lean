-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFinite_lineVar_natDegree_coeff_0f4cef3db7dd
-- name    : P2M_GroundTheory_Heights__Heights_ChartFinite_lineVar_natDegree_coeff_0f4cef3db7dd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:10.497445+00:00
-- url     : https://prove2.me/theorems/37526ad4-a2e1-4bff-9ff8-f691a35e73c7
-- title:
--   P2 M Ground Theory Heights  Heights Chart Finite line Var nat Degree coeff 0f4cef3db7dd: P2 M Ground Theory Heights  Heights Chart Finite line Var nat Degree coeff 0f4cef3db7dd
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Finite line Var nat Degree coeff 0f4cef3db7dd construction uses the P2 M Ground Theory Heights  Heights Chart Finite line Var nat Degree coeff 0f4cef3db7dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFinite.lean#L42-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFinite.lean#L42-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PFGNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFinite
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
open GroundTheory.Heights₂.Heights.ChartFinite
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartFinite_lineVar_natDegree_coeff_0f4cef3db7dd (t : Fin n → F) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineVar t m ij).natDegree ≤ groupWeight (e + 1) n ij 0 ∧
      (lineVar t m ij).coeff (groupWeight (e + 1) n ij 0) = specFirstVar t ij := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFinite».«lineVar_natDegree_coeff» := P2M_GroundTheory_Heights__Heights_ChartFinite_lineVar_natDegree_coeff_0f4cef3db7dd
