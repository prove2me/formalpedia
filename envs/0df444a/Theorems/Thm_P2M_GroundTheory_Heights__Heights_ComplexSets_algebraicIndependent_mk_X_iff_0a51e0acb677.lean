-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_algebraicIndependent_mk_X_iff_0a51e0acb677
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_algebraicIndependent_mk_X_iff_0a51e0acb677
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:38.557275+00:00
-- url     : https://prove2.me/theorems/cfe42d01-41b4-4d9f-9421-6dc410575016
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets algebraic Independent mk X iff 0a51e0acb677: P2 M Ground Theory Heights  Heights Complex Sets algebraic Independent mk X iff 0a51e0acb677
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets algebraic Independent mk X iff 0a51e0acb677 construction uses the P2 M Ground Theory Heights  Heights Complex Sets algebraic Independent mk X iff 0a51e0acb677 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L43-L47

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_algebraicIndependent_mk_X_iff_0a51e0acb677 (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n)) :
    AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) ↔
      ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ I → q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«algebraicIndependent_mk_X_iff» := P2M_GroundTheory_Heights__Heights_ComplexSets_algebraicIndependent_mk_X_iff_0a51e0acb677
