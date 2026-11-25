-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_unit_all_01d1868a230d
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_unit_all_01d1868a230d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:12.44639+00:00
-- url     : https://prove2.me/theorems/c110aa6d-bb71-5ba8-b4cd-79564a0e57a9
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists unit all 01d1868a230d: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists unit all 01d1868a230d
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists unit all 01d1868a230d construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists unit all 01d1868a230d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L262-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L262-L305

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_unit_all_01d1868a230d (hy : IsArithVar (mCoordIdeal y) 1) (S : Finset (HeightOneSpectrum (𝓞 K'))) :
    ∃ (d : ℕ) (G : K'), 1 ≤ d ∧ G ≠ 0 ∧ G ∈ chartLat y 1 d ∧ ∀ P ∈ S, IsUnitAt y P d G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«exists_unit_all» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_unit_all_01d1868a230d
