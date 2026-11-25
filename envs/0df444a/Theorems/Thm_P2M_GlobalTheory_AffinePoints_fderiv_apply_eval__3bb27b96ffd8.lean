-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AffinePoints_fderiv_apply_eval__3bb27b96ffd8
-- name    : P2M_GlobalTheory_AffinePoints_fderiv_apply_eval__3bb27b96ffd8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:00.380156+00:00
-- url     : https://prove2.me/theorems/f0cfcf34-770a-44d1-8795-8cef410f97c4
-- title:
--   P2 M Global Theory Affine Points fderiv apply eval  3bb27b96ffd8: P2 M Global Theory Affine Points fderiv apply eval  3bb27b96ffd8
-- statement:
--   The P2 M Global Theory Affine Points fderiv apply eval  3bb27b96ffd8 construction uses the P2 M Global Theory Affine Points fderiv apply eval  3bb27b96ffd8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L333-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L333-L348

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {φ : E → (A →ₐ[ℂ] ℂ)}

theorem P2M_GlobalTheory_AffinePoints_fderiv_apply_eval__3bb27b96ffd8 {R : Type*} [CommRing R] (g : R →+* A) {z : E}
    (hφ : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z) (v : E)
    (hv : ∀ r, fderiv ℂ (fun z => φ z (g r)) z v = 0) (a : A) (h : Polynomial R) :
    fderiv ℂ (fun z => φ z (h.eval₂ g a)) z v =
      φ z ((Polynomial.derivative h).eval₂ g a) * fderiv ℂ (fun z => φ z a) z v := by sorry

alias «GlobalTheory».«AffinePoints».«fderiv_apply_eval₂» := P2M_GlobalTheory_AffinePoints_fderiv_apply_eval__3bb27b96ffd8
