-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_iA_succ_e16bc66519a8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_iA_succ_e16bc66519a8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:22.934434+00:00
-- url     : https://prove2.me/theorems/9909d703-fecd-4741-ad63-7b0a91a5bdb6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES ker i A succ e16bc66519a8: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is S
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES ker i A succ e16bc66519a8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES ker i A succ e16bc66519a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L279-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L279-L304

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_iA_succ_e16bc66519a8 (n : ℕ) : LinearMap.ker (H.iA (n + 1)) = LinearMap.range (H.delta n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«EulerSES».«IsSES».«ker_iA_succ» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_iA_succ_e16bc66519a8
