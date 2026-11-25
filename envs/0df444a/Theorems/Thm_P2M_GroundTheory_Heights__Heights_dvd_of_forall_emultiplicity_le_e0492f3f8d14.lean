-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_dvd_of_forall_emultiplicity_le_e0492f3f8d14
-- name    : P2M_GroundTheory_Heights__Heights_dvd_of_forall_emultiplicity_le_e0492f3f8d14
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:54.067503+00:00
-- url     : https://prove2.me/theorems/c72ee6cb-800c-4651-bfad-e58acfc08248
-- title:
--   P2 M Ground Theory Heights  Heights dvd of forall emultiplicity le e0492f3f8d14: P2 M Ground Theory Heights  Heights dvd of forall emultiplicity le e0492f3f8d14
-- statement:
--   The P2 M Ground Theory Heights  Heights dvd of forall emultiplicity le e0492f3f8d14 construction uses the P2 M Ground Theory Heights  Heights dvd of forall emultiplicity le e0492f3f8d14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormSection.lean#L31-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormSection.lean#L31-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
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
variable {F : Type*} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_dvd_of_forall_emultiplicity_le_e0492f3f8d14 {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p, Irreducible p → emultiplicity p a ≤ emultiplicity p b) : a ∣ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«dvd_of_forall_emultiplicity_le» := P2M_GroundTheory_Heights__Heights_dvd_of_forall_emultiplicity_le_e0492f3f8d14
