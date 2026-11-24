-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartProjMatrix_mulVec_44e4e5c17922
-- name    : P2M_GroundTheory_Heights__Heights_chartProjMatrix_mulVec_44e4e5c17922
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:32.919796+00:00
-- url     : https://prove2.me/theorems/f35fa96d-e2c9-4617-a200-ee8a96570265
-- title:
--   P2 M Ground Theory Heights  Heights chart Proj Matrix mul Vec 44e4e5c17922: P2 M Ground Theory Heights  Heights chart Proj Matrix mul Vec 44e4e5c17922
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Proj Matrix mul Vec 44e4e5c17922 construction uses the P2 M Ground Theory Heights  Heights chart Proj Matrix mul Vec 44e4e5c17922 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartProjObjects.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartProjObjects.lean#L24-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_chartProjMatrix_mulVec_44e4e5c17922 {m d : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ)) (x : Fin m → ℂ) (r : Fin d) :
    (chartProjMatrix σ Ψ *ᵥ x) r = Ψ (fun i' => x (σ.symm i')) r.succ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartProjMatrix_mulVec» := P2M_GroundTheory_Heights__Heights_chartProjMatrix_mulVec_44e4e5c17922
