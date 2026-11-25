-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_eval_pderiv_sum_mul_8d82014868a9
-- name    : P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_eval_pderiv_sum_mul_8d82014868a9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:46:52.327802+00:00
-- url     : https://prove2.me/theorems/b5583971-935a-4a30-a566-0e13cca1640a
-- title:
--   P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface eval pderiv sum mul 8d82014868a9: P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface eval pderiv sum mul 8d82014868a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface eval pderiv sum mul 8d82014868a9 construction uses the P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface eval pderiv sum mul 8d82014868a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PJacobianRankOffHypersurface.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PJacobianRankOffHypersurface.lean#L14-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianRankOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PJacobianRankOffHypersurface
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

theorem P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_eval_pderiv_sum_mul_8d82014868a9 {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (c g : ι → MvPolynomial σ ℂ) (hg : ∀ k, eval w (g k) = 0) (x : σ) :
    eval w (pderiv x (∑ k, c k * g k)) = ∑ k, eval w (c k) * eval w (pderiv x (g k)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«JacobianRankOffHypersurface».«eval_pderiv_sum_mul» := P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_eval_pderiv_sum_mul_8d82014868a9
