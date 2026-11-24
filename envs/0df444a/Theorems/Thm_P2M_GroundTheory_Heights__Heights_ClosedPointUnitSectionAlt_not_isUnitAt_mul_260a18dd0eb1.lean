-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_mul_260a18dd0eb1
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_mul_260a18dd0eb1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:53.07399+00:00
-- url     : https://prove2.me/theorems/5cf6e489-c8a2-44ae-8a84-3e43e48686d4
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt not is Unit At mul 260a18dd0eb1: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt not is Unit At mul 260a18dd0eb1
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt not is Unit At mul 260a18dd0eb1 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt not is Unit At mul 260a18dd0eb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L141-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L141-L152

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_mul_260a18dd0eb1 (hy : IsArithVar (mCoordIdeal y) 1) {P : HeightOneSpectrum (𝓞 K')} {a b : ℕ}
    {g h : K'} (hg : ¬IsUnitAt y P a g) (hh : h ∈ chartLat y 1 b) : ¬IsUnitAt y P (a + b) (g * h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«not_isUnitAt_mul» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_mul_260a18dd0eb1
