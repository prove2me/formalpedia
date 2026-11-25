-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_finrank_of_generators_fbbde75efc83
-- name    : P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_finrank_of_generators_fbbde75efc83
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:51:42.327654+00:00
-- url     : https://prove2.me/theorems/d5d257b9-4124-5256-ad9b-5063398b6f2e
-- title:
--   P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface finrank of generators fbbde75efc83: P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface finrank of generators fbbde75e
-- statement:
--   The P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface finrank of generators fbbde75efc83 construction uses the P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface finrank of generators fbbde75efc83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PJacobianRankOffHypersurface.lean#L36-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PJacobianRankOffHypersurface.lean#L36-L66

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

theorem P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_finrank_of_generators_fbbde75efc83 {σ ι : Type*} [Fintype σ] [Fintype ι]
    (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ) (t : MvPolynomial σ ℂ)
    (hqQ : ∀ j, q j ∈ Q) (hgen : ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q))
    (f : ι → MvPolynomial σ ℂ) (s δ : MvPolynomial σ ℂ) (hfQ : ∀ k, f k ∈ Q)
    (hs : ∀ p ∈ Q, s * p ∈ Ideal.span (Set.range f))
    (hδ : ∀ w : σ → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k x ↦ eval w (pderiv x (f k)))
    (hcard : Fintype.card ι + d = Fintype.card σ) (w : σ → ℂ) (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q)
    (hμ : eval w (s * t * δ) ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j)))) + d =
      Fintype.card σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«JacobianRankOffHypersurface».«finrank_of_generators» := P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_finrank_of_generators_fbbde75efc83
