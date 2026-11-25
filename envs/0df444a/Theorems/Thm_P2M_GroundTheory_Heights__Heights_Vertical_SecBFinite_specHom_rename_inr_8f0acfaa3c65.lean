-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inr_8f0acfaa3c65
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inr_8f0acfaa3c65
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:54.899299+00:00
-- url     : https://prove2.me/theorems/892136a4-d293-4902-88c9-a2df64b05a35
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom rename inr 8f0acfaa3c65: P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom rename inr 8f0acfaa3c65
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom rename inr 8f0acfaa3c65 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom rename inr 8f0acfaa3c65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L224-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L224-L237

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inr_8f0acfaa3c65 (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) :
    specHom e n v (rename Sum.inr g) =
      C (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (parIdx e n) g)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«specHom_rename_inr» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inr_8f0acfaa3c65
