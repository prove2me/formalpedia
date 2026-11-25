-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_d36d759dd77d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_d36d759dd77d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:15.723407+00:00
-- url     : https://prove2.me/theorems/99436ff5-9208-4e79-b35d-060c94e0074d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman quot Laurent smul eq zero d36d759dd77d: P2 M Ground Theory Heights  Heights Kleiman quot Laurent smul eq zero d36d759dd77d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman quot Laurent smul eq zero d36d759dd77d construction uses the P2 M Ground Theory Heights  Heights Kleiman quot Laurent smul eq zero d36d759dd77d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L275-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L275-L280

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_d36d759dd77d {p : Poly S N} (hp : p ∈ primeOf (S := S) x) (y : quotLaurent M₁ M₂) :
    p • y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«quotLaurent_smul_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_d36d759dd77d
