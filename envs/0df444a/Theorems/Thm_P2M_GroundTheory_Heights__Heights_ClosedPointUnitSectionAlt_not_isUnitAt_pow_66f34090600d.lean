-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_pow_66f34090600d
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_pow_66f34090600d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:36:15.473288+00:00
-- url     : https://prove2.me/theorems/f1d2aee1-7a63-4c83-9419-04b61f52fd61
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt not is Unit At pow 66f34090600d: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt not is Unit At pow 66f34090600d
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt not is Unit At pow 66f34090600d construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt not is Unit At pow 66f34090600d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L154-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L154-L163

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_pow_66f34090600d (hy : IsArithVar (mCoordIdeal y) 1) {P : HeightOneSpectrum (𝓞 K')} {a : ℕ}
    {g : K'} (hg : ¬IsUnitAt y P a g) (hga : g ∈ chartLat y 1 a) (n : ℕ) :
    ¬IsUnitAt y P (a * (n + 1)) (g ^ (n + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«not_isUnitAt_pow» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_pow_66f34090600d
