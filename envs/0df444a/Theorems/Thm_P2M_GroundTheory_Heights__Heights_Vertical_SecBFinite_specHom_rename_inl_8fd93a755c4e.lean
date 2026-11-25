-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inl_8fd93a755c4e
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inl_8fd93a755c4e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:02.330921+00:00
-- url     : https://prove2.me/theorems/73d3eee3-114b-4a6a-ac65-2211cc3490c8
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom rename inl 8fd93a755c4e: P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom rename inl 8fd93a755c4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom rename inl 8fd93a755c4e construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom rename inl 8fd93a755c4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L208-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L208-L215

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inl_8fd93a755c4e (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (p : MvPolynomial (Fin n) (𝓞 K)) :
    specHom e n v (rename Sum.inl p) = MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«specHom_rename_inl» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inl_8fd93a755c4e
