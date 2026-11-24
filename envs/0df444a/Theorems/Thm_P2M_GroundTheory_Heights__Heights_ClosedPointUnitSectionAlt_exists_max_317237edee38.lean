-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_max_317237edee38
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_max_317237edee38
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:10.739404+00:00
-- url     : https://prove2.me/theorems/3d1f9085-7160-4132-86f7-2b42fd2991cc
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists max 317237edee38: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists max 317237edee38
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists max 317237edee38 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists max 317237edee38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L103-L111

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_max_317237edee38 (hy : IsArithVar (mCoordIdeal y) 1) (P : HeightOneSpectrum (𝓞 K')) :
    ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧ ∀ u, P.valuation K' (y ⟨(), u⟩) ≤ P.valuation K' (y ⟨(), t⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«exists_max» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_max_317237edee38
