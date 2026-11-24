-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_exists_ne_zero_of_span_5f8e06e12f5c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_exists_ne_zero_of_span_5f8e06e12f5c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:40.328852+00:00
-- url     : https://prove2.me/theorems/6d5aea66-1edb-403b-b1fb-c1de13d072e0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim exists ne zero of span 5f8e06e12f5c: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim exists ne zero of
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim exists ne zero of span 5f8e06e12f5c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim exists ne zero of span 5f8e06e12f5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDim.lean#L57-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDim.lean#L57-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairBundleTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim
variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {K : Type*} [DecidableEq K]
  {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_exists_ne_zero_of_span_5f8e06e12f5c {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (hN : 0 < N) (e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) :
    ∃ l, ∑ i, t i * algebraMap Ω Φ (ψ l (e i)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDim».«exists_ne_zero_of_span» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_exists_ne_zero_of_span_5f8e06e12f5c
