-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integer_of_mem_chartRingZ_a503b6b08454
-- name    : P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integer_of_mem_chartRingZ_a503b6b08454
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:36.461136+00:00
-- url     : https://prove2.me/theorems/91221d38-cdde-4d1d-b673-a114e8b713d4
-- title:
--   P2 M Ground Theory Heights  Heights Curve Affine Charts mem integer of mem chart Ring Z a503b6b08454: P2 M Ground Theory Heights  Heights Curve Affine Charts mem integer of mem chart Ring Z a503b6b084
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Affine Charts mem integer of mem chart Ring Z a503b6b08454 construction uses the P2 M Ground Theory Heights  Heights Curve Affine Charts mem integer of mem chart Ring Z a503b6b08454 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L23-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCurveCharts.lean#L23-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.CurveAffineCharts
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integer_of_mem_chartRingZ_a503b6b08454 [NumberField K'] (v : HeightOneSpectrum (𝓞 K')) (t : T)
    (ht : ∀ u, v.valuation K' (y ⟨(), u⟩) ≤ v.valuation K' (y ⟨(), t⟩)) {b : K'}
    (hb : b ∈ chartRingZ y (fun _ => t)) : b ∈ (v.valuation K').integer := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveAffineCharts».«mem_integer_of_mem_chartRingZ» := P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integer_of_mem_chartRingZ_a503b6b08454
