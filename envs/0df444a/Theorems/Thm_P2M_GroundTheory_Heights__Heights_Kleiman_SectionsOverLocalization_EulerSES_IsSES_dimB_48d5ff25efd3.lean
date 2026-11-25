-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_dimB_48d5ff25efd3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_dimB_48d5ff25efd3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:15.697039+00:00
-- url     : https://prove2.me/theorems/f1764c48-be9d-4d7a-bb28-32baf7a81a3a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES dim B 48d5ff25efd3: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES dim
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES dim B 48d5ff25efd3 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES dim B 48d5ff25efd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L322-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L322-L325

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CohMkEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
open Module
variable {F : Type} [Field F] {A B C : ℕ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]
  [∀ n, AddCommGroup (B n)] [∀ n, Module F (B n)] [∀ n, AddCommGroup (C n)] [∀ n, Module F (C n)]
variable {CA : ∀ n, Submodule F (A n)} {CB : ∀ n, Submodule F (B n)} {CC : ∀ n, Submodule F (C n)}
  {dA : ∀ n, A n →ₗ[F] A (n + 1)} {dB : ∀ n, B n →ₗ[F] B (n + 1)} {dC : ∀ n, C n →ₗ[F] C (n + 1)}
  {f : ∀ n, A n →ₗ[F] B n} {g : ∀ n, B n →ₗ[F] C n}
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES.IsSES
variable (H : IsSES CA CB CC dA dB dC f g)
include H
variable (hfa : ∀ n, FiniteDimensional F (coh CA dA n)) (hfb : ∀ n, FiniteDimensional F (coh CB dB n))
  (hfc : ∀ n, FiniteDimensional F (coh CC dC n))
include hfb

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_dimB_48d5ff25efd3 (n : ℕ) :
    finrank F (coh CB dB n) = finrank F (LinearMap.range (H.pB n)) + finrank F (LinearMap.range (H.iA n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«EulerSES».«IsSES».«dimB» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_dimB_48d5ff25efd3
