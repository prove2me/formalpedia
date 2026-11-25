-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_X_inl_7dae525d82ab
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_X_inl_7dae525d82ab
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:07.432797+00:00
-- url     : https://prove2.me/theorems/ed425b56-35bb-519d-a1ee-87db521ffc87
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom X inl 7dae525d82ab: P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom X inl 7dae525d82ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom X inl 7dae525d82ab construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom X inl 7dae525d82ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L203-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L203-L205

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_X_inl_7dae525d82ab (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K)) (j : Fin n) :
    specHom e n v (X (Sum.inl j)) = X j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«specHom_X_inl» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_X_inl_7dae525d82ab
