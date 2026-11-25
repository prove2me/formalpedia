-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_fc9d93ee6b76
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_fc9d93ee6b76
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:19.19708+00:00
-- url     : https://prove2.me/theorems/90201778-e1b1-4762-a68f-75c2ed070ca4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman quot Proj smul iota fc9d93ee6b76: P2 M Ground Theory Heights  Heights Kleiman quot Proj smul iota fc9d93ee6b76
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman quot Proj smul iota fc9d93ee6b76 construction uses the P2 M Ground Theory Heights  Heights Kleiman quot Proj smul iota fc9d93ee6b76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L357-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L357-L365

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
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
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)
variable {M₁ M₂}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_fc9d93ee6b76 (r : Poly S N) {e : ℤ} (g : M₁.piece e) (c : ℤ) :
    quotProj M₁ M₂ c (r • quotIota M₁ M₂ e g) = ∑ i ∈ Finset.range (r.totalDegree + 1),
      if e + i = c then homogeneousComponent i r • quotIota M₁ M₂ e g else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«quotProj_smul_iota» := P2M_GroundTheory_Heights__Heights_Kleiman_quotProj_smul_iota_fc9d93ee6b76
