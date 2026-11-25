-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_pow_sub_one_ab4b1a690500
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_pow_sub_one_ab4b1a690500
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:27.762798+00:00
-- url     : https://prove2.me/theorems/047060b4-9937-5cee-bfd8-6fd21721e76f
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists pow sub one ab4b1a690500: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists pow sub one ab4b1a690500
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists pow sub one ab4b1a690500 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists pow sub one ab4b1a690500 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L174-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L174-L204

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
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_pow_sub_one_ab4b1a690500 (P : HeightOneSpectrum (𝓞 K')) {x : K'} (hx : P.valuation K' x = 1) :
    ∃ N : ℕ, 1 ≤ N ∧ P.valuation K' (x ^ N - 1) < 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«exists_pow_sub_one» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_pow_sub_one_ab4b1a690500
