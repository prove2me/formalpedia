-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_exists_fin_ec031f113fa3
-- name    : P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_exists_fin_ec031f113fa3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:47:00.4808+00:00
-- url     : https://prove2.me/theorems/48d3e90d-c3de-4c5c-bbbc-fa0e2c600e63
-- title:
--   P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface exists fin ec031f113fa3: P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface exists fin ec031f113fa3
-- statement:
--   The P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface exists fin ec031f113fa3 construction uses the P2 M Ground Theory Heights  Heights Jacobian Rank Off Hypersurface exists fin ec031f113fa3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PJacobianRankOffHypersurface.lean#L68-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PJacobianRankOffHypersurface.lean#L68-L92

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

theorem P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_exists_fin_ec031f113fa3 (hF : FrameJacobianGeneric.Statement) {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) :
    ∃ (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s δ : MvPolynomial (Fin n) ℂ),
      Fintype.card {j // j ∉ I₀} + d = n ∧ (∀ k, f k ∈ J) ∧ s ∉ J ∧ δ ∉ J ∧
        (∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)) ∧
        ∀ w : Fin n → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k l ↦ eval w (pderiv l (f k)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«JacobianRankOffHypersurface».«exists_fin» := P2M_GroundTheory_Heights__Heights_JacobianRankOffHypersurface_exists_fin_ec031f113fa3
