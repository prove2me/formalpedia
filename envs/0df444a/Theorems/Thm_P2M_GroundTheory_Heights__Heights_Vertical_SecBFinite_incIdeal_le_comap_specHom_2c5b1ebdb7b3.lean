-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_comap_specHom_2c5b1ebdb7b3
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_comap_specHom_2c5b1ebdb7b3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:18.425355+00:00
-- url     : https://prove2.me/theorems/b0ae7b50-2db3-4ed0-a97a-8e5cbc718b22
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite inc Ideal le comap spec Hom 2c5b1ebdb7b3: P2 M Ground Theory Heights  Heights Vertical Sec BFinite inc Ideal le comap spec Hom 2c5b1ebdb7b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite inc Ideal le comap spec Hom 2c5b1ebdb7b3 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite inc Ideal le comap spec Hom 2c5b1ebdb7b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L241-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L241-L258

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_comap_specHom_2c5b1ebdb7b3 (e : ℕ) {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)) :
    incIdeal (integralModel I) (e + 1) ≤
      (modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v))) ⊔
        Ideal.span {chartForm (parY e n v)}).comap (specHom e n v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«incIdeal_le_comap_specHom» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_comap_specHom_2c5b1ebdb7b3
