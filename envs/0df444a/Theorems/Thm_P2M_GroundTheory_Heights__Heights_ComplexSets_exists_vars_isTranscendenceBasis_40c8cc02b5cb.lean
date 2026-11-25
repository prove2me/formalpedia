-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_exists_vars_isTranscendenceBasis_40c8cc02b5cb
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_exists_vars_isTranscendenceBasis_40c8cc02b5cb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:16.973546+00:00
-- url     : https://prove2.me/theorems/8da086cd-1e8c-40b6-9e22-e3eb1607de09
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets exists vars is Transcendence Basis 40c8cc02b5cb: P2 M Ground Theory Heights  Heights Complex Sets exists vars is Transcendence Basis 40c8cc02b5cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets exists vars is Transcendence Basis 40c8cc02b5cb construction uses the P2 M Ground Theory Heights  Heights Complex Sets exists vars is Transcendence Basis 40c8cc02b5cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L88-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L88-L109

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
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
open MvPolynomial
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_exists_vars_isTranscendenceBasis_40c8cc02b5cb (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime] :
    ∃ u : Set (Fin n), AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk P (X (i : Fin n))) ∧
      Cardinal.mk u = Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«exists_vars_isTranscendenceBasis» := P2M_GroundTheory_Heights__Heights_ComplexSets_exists_vars_isTranscendenceBasis_40c8cc02b5cb
