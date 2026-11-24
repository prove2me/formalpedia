-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_le_of_mem_add946ce0df5
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_le_of_mem_add946ce0df5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:52.307302+00:00
-- url     : https://prove2.me/theorems/f333e8c6-4ed5-4c9a-8616-4502b2f30616
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt le of mem add946ce0df5: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt le of mem add946ce0df5
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt le of mem add946ce0df5 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt le of mem add946ce0df5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L115-L121

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_le_of_mem_add946ce0df5 {P : HeightOneSpectrum (𝓞 K')} {t : T} (ht0 : y ⟨(), t⟩ ≠ 0)
    (ht : ∀ u, P.valuation K' (y ⟨(), u⟩) ≤ P.valuation K' (y ⟨(), t⟩)) {d : ℕ} {g : K'}
    (hg : g ∈ chartLat y 1 d) : P.valuation K' g ≤ P.valuation K' (y ⟨(), t⟩) ^ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«le_of_mem» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_le_of_mem_add946ce0df5
