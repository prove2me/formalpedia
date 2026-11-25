-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_sep_7bec6285acde
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_sep_7bec6285acde
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:59.676129+00:00
-- url     : https://prove2.me/theorems/5f10903a-6c5f-4095-a55d-d1acd2e96440
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists sep 7bec6285acde: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists sep 7bec6285acde
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists sep 7bec6285acde construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists sep 7bec6285acde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L206-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L206-L240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_sep_7bec6285acde (hy : IsArithVar (mCoordIdeal y) 1) {P P' : HeightOneSpectrum (𝓞 K')} {d : ℕ}
    {G : K'} (hG : G ∈ chartLat y 1 d) (h1 : IsUnitAt y P' d G) (h2 : ¬IsUnitAt y P d G) :
    ∃ (k : ℕ) (h : K'), h ∈ chartLat y 1 k ∧ IsUnitAt y P k h ∧ ¬IsUnitAt y P' k h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«exists_sep» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_sep_7bec6285acde
