-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_grad_mem_span_406acfd04172
-- name    : P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_grad_mem_span_406acfd04172
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:49:05.824615+00:00
-- url     : https://prove2.me/theorems/8e45fe76-c28f-5d70-93a9-f44926d9597d
-- title:
--   P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface grad mem span 406acfd04172: P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface grad mem span 406acfd04172
-- statement:
--   The P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface grad mem span 406acfd04172 construction uses the P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface grad mem span 406acfd04172 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PJacobianRankOffHypersurface.lean#L19-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PJacobianRankOffHypersurface.lean#L19-L34

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

theorem P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_grad_mem_span_406acfd04172 {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (a p : MvPolynomial σ ℂ) (c g : ι → MvPolynomial σ ℂ) (hsum : ∑ k, c k * g k = a * p)
    (hg : ∀ k, eval w (g k) = 0) (hp : eval w p = 0) (ha : eval w a ≠ 0) :
    (fun x ↦ eval w (pderiv x p)) ∈
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (g k))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«JacobianRankOffHypersurface».«grad_mem_span» := P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_grad_mem_span_406acfd04172
