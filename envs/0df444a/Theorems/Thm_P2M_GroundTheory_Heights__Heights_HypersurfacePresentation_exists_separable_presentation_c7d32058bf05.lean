-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_separable_presentation_c7d32058bf05
-- name    : P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_separable_presentation_c7d32058bf05
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:44.572868+00:00
-- url     : https://prove2.me/theorems/413834fc-ddb4-47d7-ad7c-d929c239e3cc
-- title:
--   P2 M Ground Theory Heights  Heights Hypersurface Presentation exists separable presentation c7d32058bf05: P2 M Ground Theory Heights  Heights Hypersurface Presentation exists separable presentation c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Hypersurface Presentation exists separable presentation c7d32058bf05 construction uses the P2 M Ground Theory Heights  Heights Hypersurface Presentation exists separable presentation c7d32058bf05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L118-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L118-L163

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
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
open GroundTheory.Heights₂.Heights.HypersurfacePresentation

theorem P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_separable_presentation_c7d32058bf05 {R A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Algebra.IsAlgebraic R A]
    {n : ℕ} (x : Fin n → A) (hx : Algebra.adjoin R (Set.range x) = ⊤) {ι : Type} [Fintype ι] (z : ι → A) :
    ∃ θ : A, (minpoly R θ).Monic ∧ (∀ H : Polynomial R, Polynomial.aeval θ H = 0 ↔ minpoly R θ ∣ H) ∧
      ∃ D : R, D ≠ 0 ∧ ∃ (q : ι → Polynomial R) (u v : Polynomial R),
      u * minpoly R θ + v * Polynomial.derivative (minpoly R θ) = Polynomial.C D ∧
      ∀ i, Polynomial.aeval θ (q i) = algebraMap R A D * z i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HypersurfacePresentation».«exists_separable_presentation» := P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_separable_presentation_c7d32058bf05
