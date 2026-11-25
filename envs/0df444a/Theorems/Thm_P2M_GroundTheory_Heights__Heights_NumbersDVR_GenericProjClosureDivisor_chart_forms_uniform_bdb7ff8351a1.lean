-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chart_forms_uniform_bdb7ff8351a1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chart_forms_uniform_bdb7ff8351a1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:14.385494+00:00
-- url     : https://prove2.me/theorems/ef0da627-1808-4897-8c0d-abea61d06f0b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor chart forms uniform bdb7ff8351a1: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor chart forms
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor chart forms uniform bdb7ff8351a1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor chart forms uniform bdb7ff8351a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L190-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L190-L210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
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
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chart_forms_uniform_bdb7ff8351a1 (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) {L : ℕ} (r : Fin L → Ω) (hr : ∀ l, r l ∈ chartRing O (segreVec y) c) :
    ∃ (n : ℕ) (U : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O), ∀ l,
      IsMultiHomog (U l) (vdeg fun _ => n) ∧
        aeval (pairProjCoord y e φ φ' t) (U l) = algebraMap Ω Φ (r l * segreVec y c ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDivisor».«chart_forms_uniform» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chart_forms_uniform_bdb7ff8351a1
