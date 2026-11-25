-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_isUnitAt_add_c542c0248662
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_isUnitAt_add_c542c0248662
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:33.873807+00:00
-- url     : https://prove2.me/theorems/15827f18-e46b-5169-85d3-16c9dc36cd43
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt is Unit At add c542c0248662: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt is Unit At add c542c0248662
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt is Unit At add c542c0248662 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt is Unit At add c542c0248662 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L165-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L165-L170

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_isUnitAt_add_c542c0248662 (hy : IsArithVar (mCoordIdeal y) 1) {P : HeightOneSpectrum (𝓞 K')} {d : ℕ}
    {g h : K'} (hg : IsUnitAt y P d g) (hh : ¬IsUnitAt y P d h) : IsUnitAt y P d (g + h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«isUnitAt_add» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_isUnitAt_add_c542c0248662
