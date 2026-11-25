-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_coh_mk_eq_904b9ec6a130
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_coh_mk_eq_904b9ec6a130
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:02.179704+00:00
-- url     : https://prove2.me/theorems/d140c9d9-c8bf-4b4d-9c03-64cde3033cb9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES coh mk eq 904b9ec6a130: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES coh mk eq 904b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES coh mk eq 904b9ec6a130 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES coh mk eq 904b9ec6a130 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L34-L37

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
variable {F : Type} [Field F] {X Y : ℕ → Type} [∀ n, AddCommGroup (X n)] [∀ n, Module F (X n)]
  [∀ n, AddCommGroup (Y n)] [∀ n, Module F (Y n)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_coh_mk_eq_904b9ec6a130 {CX : ∀ n, Submodule F (X n)} {dX : ∀ n, X n →ₗ[F] X (n + 1)} {n : ℕ}
    (x y : cyc CX dX n) :
    (Submodule.Quotient.mk x : coh CX dX n) = Submodule.Quotient.mk y ↔ (x : X n) - y ∈ bnd CX dX n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«EulerSES».«coh_mk_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_coh_mk_eq_904b9ec6a130
