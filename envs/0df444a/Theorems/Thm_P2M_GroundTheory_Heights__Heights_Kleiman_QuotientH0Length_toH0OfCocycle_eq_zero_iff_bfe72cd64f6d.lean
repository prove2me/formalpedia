-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toH0OfCocycle_eq_zero_iff_bfe72cd64f6d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toH0OfCocycle_eq_zero_iff_bfe72cd64f6d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:47.240717+00:00
-- url     : https://prove2.me/theorems/41bae31e-a235-518c-94ea-88311ef06d61
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length to H0 Of Cocycle eq zero iff bfe72cd64f6d: P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length to H0 Of Cocycle eq zero iff bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length to H0 Of Cocycle eq zero iff bfe72cd64f6d construction uses the P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length to H0 Of Cocycle eq zero iff bfe72cd64f6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L25-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LengthQuotientEqLengthH0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toH0OfCocycle_eq_zero_iff_bfe72cd64f6d (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) (m : M) :
    toH0OfCocycle φ hφ m = 0 ↔ φ m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotientH0Length».«toH0OfCocycle_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toH0OfCocycle_eq_zero_iff_bfe72cd64f6d
