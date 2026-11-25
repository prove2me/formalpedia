-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_update_comp_swap_bf4bc8283636
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_update_comp_swap_bf4bc8283636
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:30.507404+00:00
-- url     : https://prove2.me/theorems/08a07217-c0dd-4308-9b07-b0e97687a010
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Symmetry update comp swap bf4bc8283636: P2 M Ground Theory Heights  Heights Chart Energy Symmetry update comp swap bf4bc8283636
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Symmetry update comp swap bf4bc8283636 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Symmetry update comp swap bf4bc8283636 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySymm.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySymm.lean#L57-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySymm
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergySymmetry

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_update_comp_swap_bf4bc8283636 {α : Type*} {n : ℕ} (Φ : Fin (n + 1) → α) (p : Fin (n + 1)) (f : α) :
    Function.update Φ p f ∘ Equiv.swap 0 p = Fin.cons f (fun i => Φ (Equiv.swap 0 p i.succ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySymmetry».«update_comp_swap» := P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_update_comp_swap_bf4bc8283636
