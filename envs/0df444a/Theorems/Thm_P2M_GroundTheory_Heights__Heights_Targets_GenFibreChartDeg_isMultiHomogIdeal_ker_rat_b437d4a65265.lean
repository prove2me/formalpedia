-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_GenFibreChartDeg_isMultiHomogIdeal_ker_rat_b437d4a65265
-- name    : P2M_GroundTheory_Heights__Heights_Targets_GenFibreChartDeg_isMultiHomogIdeal_ker_rat_b437d4a65265
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:18.578232+00:00
-- url     : https://prove2.me/theorems/5c28dd31-e007-4341-b3bd-800af0d6e597
-- title:
--   P2 M Ground Theory Heights  Heights Targets Gen Fibre Chart Deg is Multi Homog Ideal ker rat b437d4a65265: P2 M Ground Theory Heights  Heights Targets Gen Fibre Chart Deg is Multi Homog Ideal ker rat
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Gen Fibre Chart Deg is Multi Homog Ideal ker rat b437d4a65265 construction uses the P2 M Ground Theory Heights  Heights Targets Gen Fibre Chart Deg is Multi Homog Ideal ker rat b437d4a65265 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGenFibreChartDeg.lean#L15-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGenFibreChartDeg.lean#L15-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GenFibreChartDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StAdjoinIndepRelfinrank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFinrankAdjoinRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGenFibreChartDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Targets_GenFibreChartDeg_isMultiHomogIdeal_ker_rat_b437d4a65265 {K' : Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (x' : (Σ k', ι' k') → Ω)
    (h : IsMultiHomogIdeal (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«GenFibreChartDeg».«isMultiHomogIdeal_ker_rat» := P2M_GroundTheory_Heights__Heights_Targets_GenFibreChartDeg_isMultiHomogIdeal_ker_rat_b437d4a65265
