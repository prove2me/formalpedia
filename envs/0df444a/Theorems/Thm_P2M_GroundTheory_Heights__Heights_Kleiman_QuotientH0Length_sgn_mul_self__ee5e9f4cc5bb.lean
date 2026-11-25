-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_sgn_mul_self__ee5e9f4cc5bb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_sgn_mul_self__ee5e9f4cc5bb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:23.085852+00:00
-- url     : https://prove2.me/theorems/3d76e5e6-4cf4-5994-ab73-290136b59b8a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length sgn mul self  ee5e9f4cc5bb: P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length sgn mul self  ee5e9f4cc5bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length sgn mul self  ee5e9f4cc5bb construction uses the P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length sgn mul self  ee5e9f4cc5bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L52-L54

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_sgn_mul_self__ee5e9f4cc5bb (L : Finset (Fin n)) (j : Fin n) : Cech.sgn L j * Cech.sgn L j = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotientH0Length».«sgn_mul_self'» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_sgn_mul_self__ee5e9f4cc5bb
