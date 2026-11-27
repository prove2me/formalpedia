-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_chartPot_7acdc5ab859e
-- name    : P2M_GroundTheory_Heights__Heights_smoothNear_chartPot_7acdc5ab859e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:48:49.053902+00:00
-- url     : https://prove2.me/theorems/170c8985-4e03-58cb-a32c-6eaa25ac59de
-- title:
--   P2 M Ground Theory Heights  Heights smooth Near chart Pot 7acdc5ab859e: P2 M Ground Theory Heights  Heights smooth Near chart Pot 7acdc5ab859e
-- statement:
--   The P2 M Ground Theory Heights  Heights smooth Near chart Pot 7acdc5ab859e construction uses the P2 M Ground Theory Heights  Heights smooth Near chart Pot 7acdc5ab859e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartProjObjects.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartProjObjects.lean#L88-L94

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_smoothNear_chartPot_7acdc5ab859e {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {T : Set (Fin m → ℂ)}
    (hT : ∀ x ∈ T, x (σ.symm i) = 1) (j : Fin e) : SmoothNear T (chartPot σ i L j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«smoothNear_chartPot» := P2M_GroundTheory_Heights__Heights_smoothNear_chartPot_7acdc5ab859e
