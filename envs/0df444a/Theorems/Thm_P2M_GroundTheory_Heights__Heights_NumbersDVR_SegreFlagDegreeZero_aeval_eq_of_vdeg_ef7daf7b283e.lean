-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_aeval_eq_of_vdeg_ef7daf7b283e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_aeval_eq_of_vdeg_ef7daf7b283e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:10.364094+00:00
-- url     : https://prove2.me/theorems/dd0e2af8-6acb-421b-aa05-432c69b2f38d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero aeval eq of vdeg ef7daf7b283e: P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero aeval eq of vdeg ef7daf7b28
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero aeval eq of vdeg ef7daf7b283e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero aeval eq of vdeg ef7daf7b283e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalEqOfVdeg.lean#L21-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalEqOfVdeg.lean#L21-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalEqOfVdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_aeval_eq_of_vdeg_ef7daf7b283e {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] {M M' : ℕ}
    {Φ : Type} [Field Φ] [Algebra O Φ] {z z' : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    (h : ∀ (k : K) (i : ι k), z ⟨some (some k), i⟩ = z' ⟨some (some k), i⟩)
    {G : MRing (bundleIdx (bundleIdx ι M) M') O} {β : K → ℕ} (hG : IsMultiHomog G (GenericProjClosureDivisor.vdeg β)) :
    aeval z G = aeval z' G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SegreFlagDegreeZero».«aeval_eq_of_vdeg» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_aeval_eq_of_vdeg_ef7daf7b283e
