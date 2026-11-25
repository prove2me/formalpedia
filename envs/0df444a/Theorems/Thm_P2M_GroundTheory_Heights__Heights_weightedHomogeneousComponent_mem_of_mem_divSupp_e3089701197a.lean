-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_weightedHomogeneousComponent_mem_of_mem_divSupp_e3089701197a
-- name    : P2M_GroundTheory_Heights__Heights_weightedHomogeneousComponent_mem_of_mem_divSupp_e3089701197a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:52:05.886807+00:00
-- url     : https://prove2.me/theorems/33a64aeb-e9f0-4b19-8938-7bdc5616ffb1
-- title:
--   P2 M Ground Theory Heights  Heights weighted Homogeneous Component mem of mem div Supp e3089701197a: P2 M Ground Theory Heights  Heights weighted Homogeneous Component mem of mem div Supp e3089701197a
-- statement:
--   The P2 M Ground Theory Heights  Heights weighted Homogeneous Component mem of mem div Supp e3089701197a construction uses the P2 M Ground Theory Heights  Heights weighted Homogeneous Component mem of mem div Supp e3089701197a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartDehom.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartDehom.lean#L22-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartDehom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartDehom
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_weightedHomogeneousComponent_mem_of_mem_divSupp_e3089701197a (x : Cone n (AlgebraicClosure ℚ))
    {s : MvPolynomial (Coord n) ℤ} {a : ι → ℕ} (hs : IsWeightedHomogeneous (coordDeg n) s a)
    {V : Ideal (MvPolynomial (Coord n) ℤ)} (hV : V ∈ Geo.divSupp (orbitIdeal x) s)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ V) (b : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) b f ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«weightedHomogeneousComponent_mem_of_mem_divSupp» := P2M_GroundTheory_Heights__Heights_weightedHomogeneousComponent_mem_of_mem_divSupp_e3089701197a
