-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chart_coord_eq_one_2829753f3694
-- name    : P2M_GroundTheory_Heights__Heights_chart_coord_eq_one_2829753f3694
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:19.965509+00:00
-- url     : https://prove2.me/theorems/44ef65a0-aeb9-4cf6-9d2e-26559564019e
-- title:
--   P2 M Ground Theory Heights  Heights chart coord eq one 2829753f3694: P2 M Ground Theory Heights  Heights chart coord eq one 2829753f3694
-- statement:
--   The P2 M Ground Theory Heights  Heights chart coord eq one 2829753f3694 construction uses the P2 M Ground Theory Heights  Heights chart coord eq one 2829753f3694 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean#L38-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing mcPts segre PBlk)
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_chart_coord_eq_one_2829753f3694 {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i)
    {x : Fin m → ℂ} (hx : x ∈ ComplexSets.zeroSet J) : x (σ.symm i) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chart_coord_eq_one» := P2M_GroundTheory_Heights__Heights_chart_coord_eq_one_2829753f3694
