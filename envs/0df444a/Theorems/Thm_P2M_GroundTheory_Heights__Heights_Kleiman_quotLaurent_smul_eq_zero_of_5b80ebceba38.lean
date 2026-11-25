-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_of_5b80ebceba38
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_of_5b80ebceba38
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:37.803672+00:00
-- url     : https://prove2.me/theorems/40e5db4e-3d36-4679-bcf3-c7e748bb9b69
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman quot Laurent smul eq zero of 5b80ebceba38: P2 M Ground Theory Heights  Heights Kleiman quot Laurent smul eq zero of 5b80ebceba38
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman quot Laurent smul eq zero of 5b80ebceba38 construction uses the P2 M Ground Theory Heights  Heights Kleiman quot Laurent smul eq zero of 5b80ebceba38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L282-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L282-L292

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_of_5b80ebceba38 {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e)
    (hJ : ∀ (a : ℤ), ∀ z ∈ M₁.piece a, aeval x f • z ∈ M₂.piece (a + e)) (y : quotLaurent M₁ M₂) :
    f • y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«quotLaurent_smul_eq_zero_of» := P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_of_5b80ebceba38
