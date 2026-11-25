-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_form_c00665a83bdb
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_form_c00665a83bdb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:02.673738+00:00
-- url     : https://prove2.me/theorems/5d21bfdd-0a91-51fd-a8a3-6891618870e4
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom form c00665a83bdb: P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom form c00665a83bdb
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom form c00665a83bdb construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite spec Hom form c00665a83bdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L218-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L218-L221

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_form_c00665a83bdb (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K)) (i : Fin (e + 1)) :
    specHom e n v (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j)) =
      linForm fun j => parY e n v (parIdx e n (i, j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«specHom_form» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_form_c00665a83bdb
