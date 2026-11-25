-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_slice_chart_fc0789027df7
-- name    : P2M_GroundTheory_Heights__Heights_GoodPointBranch_slice_chart_fc0789027df7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:55.231035+00:00
-- url     : https://prove2.me/theorems/b61030ef-402b-56d1-94b3-366a6c00c6b4
-- title:
--   P2 M Ground Theory Heights  Heights Good Point Branch slice chart fc0789027df7: P2 M Ground Theory Heights  Heights Good Point Branch slice chart fc0789027df7
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Point Branch slice chart fc0789027df7 construction uses the P2 M Ground Theory Heights  Heights Good Point Branch slice chart fc0789027df7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L74-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L74-L151

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
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
open MvPolynomial Filter Topology Matrix ComplexSets Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.GoodPointBranch

theorem P2M_GroundTheory_Heights__Heights_GoodPointBranch_slice_chart_fc0789027df7 {d n : ℕ} {ψ : (Fin (d + 1) → ℂ) → Fin n → ℂ} {D : (Fin (d + 1) → ℂ) →L[ℂ] Fin n → ℂ}
    {q : Fin n → ℂ} {S : Set (Fin n → ℂ)} {A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)} {O : Set (Fin d → ℂ)}
    {V : Set (Fin n → ℂ)} {g : (Fin d → ℂ) → Fin n → ℂ}
    (hψ : HasStrictFDerivAt ψ D 0) (hψ0 : ψ 0 = q) (hD : ∀ v, v 0 = 0 → D v = 0 → v = 0)
    (hV : IsOpen V) (hqV : q ∈ V) (hg : AnalyticOnNhd ℂ g O) (hAg : ∀ y ∈ O, A (g y) = y)
    (hS : S ∩ V = g '' O) (hslice : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), ψ (consZero d v) ∈ S) :
    (∀ v, v 0 = 0 → A (D v) = 0 → v = 0) ∧
    ∃ W ∈ 𝓝 (0 : Fin d → ℂ), Set.InjOn (fun v => ψ (consZero d v)) W ∧
      ∀ W' ∈ 𝓝 (0 : Fin d → ℂ), W' ⊆ W → ∃ N ∈ 𝓝 q, S ∩ N ⊆ (fun v => ψ (consZero d v)) '' W' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodPointBranch».«slice_chart» := P2M_GroundTheory_Heights__Heights_GoodPointBranch_slice_chart_fc0789027df7
