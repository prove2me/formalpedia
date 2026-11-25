-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_delta_8ea97096ed60
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_delta_8ea97096ed60
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:52.500804+00:00
-- url     : https://prove2.me/theorems/39494971-4ad9-491c-955e-865e85d43ccd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES ker delta 8ea97096ed60: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES ker delta 8ea97096ed60 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES Is SES ker delta 8ea97096ed60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L248-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L248-L277

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_delta_8ea97096ed60 (n : ℕ) : LinearMap.ker (H.delta n) = LinearMap.range (H.pB n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«EulerSES».«IsSES».«ker_delta» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_delta_8ea97096ed60
