-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_analyticAt_eval_map_2cf0cf611716
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_analyticAt_eval_map_2cf0cf611716
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:23.557365+00:00
-- url     : https://prove2.me/theorems/e42ed86a-0fc7-4b8b-b12b-1d6b0ba2b725
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets analytic At eval map 2cf0cf611716: P2 M Ground Theory Heights  Heights Complex Sets analytic At eval map 2cf0cf611716
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets analytic At eval map 2cf0cf611716 construction uses the P2 M Ground Theory Heights  Heights Complex Sets analytic At eval map 2cf0cf611716 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSimpleRootBranch.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSimpleRootBranch.lean#L17-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSimpleRootBranch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Filter Topology
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_analyticAt_eval_map_2cf0cf611716 {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (v : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«analyticAt_eval_map» := P2M_GroundTheory_Heights__Heights_ComplexSets_analyticAt_eval_map_2cf0cf611716
