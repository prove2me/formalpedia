-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_segreChartComponents_1a9d50ef3666
-- name    : P2M_GroundTheory_Heights__Heights_mem_segreChartComponents_1a9d50ef3666
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:25.796543+00:00
-- url     : https://prove2.me/theorems/7361ee8a-6f19-48db-9b57-99cffeca8691
-- title:
--   P2 M Ground Theory Heights  Heights mem segre Chart Components 1a9d50ef3666: P2 M Ground Theory Heights  Heights mem segre Chart Components 1a9d50ef3666
-- statement:
--   The P2 M Ground Theory Heights  Heights mem segre Chart Components 1a9d50ef3666 construction uses the P2 M Ground Theory Heights  Heights mem segre Chart Components 1a9d50ef3666 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartObjects.lean#L31-L34

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

theorem P2M_GroundTheory_Heights__Heights_mem_segreChartComponents_1a9d50ef3666 {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} :
    J ∈ segreChartComponents P σ i ↔ J ∈ (segreChartIdeal P σ i).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_segreChartComponents» := P2M_GroundTheory_Heights__Heights_mem_segreChartComponents_1a9d50ef3666
