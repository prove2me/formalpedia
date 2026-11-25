-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_eval_map_eval_eq_sum_bb3ac0c02484
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_eval_map_eval_eq_sum_bb3ac0c02484
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:54.905799+00:00
-- url     : https://prove2.me/theorems/a03e8565-0dc7-5226-ab45-4b44711fa5e8
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets eval map eval eq sum bb3ac0c02484: P2 M Ground Theory Heights  Heights Complex Sets eval map eval eq sum bb3ac0c02484
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets eval map eval eq sum bb3ac0c02484 construction uses the P2 M Ground Theory Heights  Heights Complex Sets eval map eval eq sum bb3ac0c02484 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSimpleRootBranch.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSimpleRootBranch.lean#L11-L15

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_eval_map_eval_eq_sum_bb3ac0c02484 {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (w : Fin d → ℂ) (s : ℂ) :
    (p.map (MvPolynomial.eval w)).eval s =
      ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval w (p.coeff i) * s ^ i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«eval_map_eval_eq_sum» := P2M_GroundTheory_Heights__Heights_ComplexSets_eval_map_eval_eq_sum_bb3ac0c02484
