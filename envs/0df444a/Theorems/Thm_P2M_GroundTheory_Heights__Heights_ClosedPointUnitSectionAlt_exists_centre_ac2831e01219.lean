-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_centre_ac2831e01219
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_centre_ac2831e01219
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:15.352905+00:00
-- url     : https://prove2.me/theorems/60accd23-a64f-5a32-ab4d-faed1bd6833e
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists centre ac2831e01219: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists centre ac2831e01219
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists centre ac2831e01219 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists centre ac2831e01219 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L343-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L343-L365

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_centre_ac2831e01219 (W : ValuationSubring K') {q : ℕ} (hq : q.Prime) (hWq : W.valuation (q : K') < 1) :
    ∃ P : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ P.asIdeal ∧
      ∀ x : K', P.valuation K' x ≤ 1 → x ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«exists_centre» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_centre_ac2831e01219
