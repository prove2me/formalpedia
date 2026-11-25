-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_mem_orbitIdeal_of_aeval_eq_zero_420291cb19c8
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_mem_orbitIdeal_of_aeval_eq_zero_420291cb19c8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:00.412499+00:00
-- url     : https://prove2.me/theorems/dc08f5ee-97a0-4355-9d1a-e99536e401e1
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max mem orbit Ideal of aeval eq zero 420291cb19c8: P2 M Ground Theory Heights  Heights Orbit Chart Max mem orbit Ideal of aeval eq zero 420291cb19c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max mem orbit Ideal of aeval eq zero 420291cb19c8 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max mem orbit Ideal of aeval eq zero 420291cb19c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L83-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L83-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
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
open GroundTheory.Heights₂.Heights.OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_mem_orbitIdeal_of_aeval_eq_zero_420291cb19c8 (x : Cone n (AlgebraicClosure ℚ))
    {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hG : IsWeightedHomogeneous (coordDeg n) G b)
    (h0 : aeval (flatCone x) G = 0) : G ∈ orbitIdeal x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«mem_orbitIdeal_of_aeval_eq_zero» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_mem_orbitIdeal_of_aeval_eq_zero_420291cb19c8
