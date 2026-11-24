-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_mul_5d9adfcd55aa
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_mul_5d9adfcd55aa
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:57.229798+00:00
-- url     : https://prove2.me/theorems/3cd5d4d5-fd96-43b6-91bf-e369b48c9dfc
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt Is Unit At mul 5d9adfcd55aa: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt Is Unit At mul 5d9adfcd55aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt Is Unit At mul 5d9adfcd55aa construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt Is Unit At mul 5d9adfcd55aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L130-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L130-L133

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_mul_5d9adfcd55aa {P : HeightOneSpectrum (𝓞 K')} {a b : ℕ} {g h : K'} (hg : IsUnitAt y P a g)
    (hh : IsUnitAt y P b h) : IsUnitAt y P (a + b) (g * h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«IsUnitAt».«mul» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_mul_5d9adfcd55aa
