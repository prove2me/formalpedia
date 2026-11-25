-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_avoid_bb0cc9dacafe
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_avoid_bb0cc9dacafe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:53.156646+00:00
-- url     : https://prove2.me/theorems/f8b8c8f3-4563-57bc-9371-0dbd09f95fa2
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists avoid bb0cc9dacafe: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists avoid bb0cc9dacafe
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists avoid bb0cc9dacafe construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists avoid bb0cc9dacafe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L242-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L242-L260

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_avoid_bb0cc9dacafe (hy : IsArithVar (mCoordIdeal y) 1) (P : HeightOneSpectrum (𝓞 K'))
    (S : Finset (HeightOneSpectrum (𝓞 K')))
    (hS : ∀ P' ∈ S, ∃ (k : ℕ) (h : K'), h ∈ chartLat y 1 k ∧ IsUnitAt y P k h ∧ ¬IsUnitAt y P' k h) :
    ∃ (k : ℕ) (z : K'), 1 ≤ k ∧ z ∈ chartLat y 1 k ∧ IsUnitAt y P k z ∧
      ∀ P' ∈ S, ¬IsUnitAt y P' k z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«exists_avoid» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_avoid_bb0cc9dacafe
