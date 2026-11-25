-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_factor_of_punctured_43801c6296a6
-- name    : P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_factor_of_punctured_43801c6296a6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:24.187503+00:00
-- url     : https://prove2.me/theorems/779cfefa-56a5-4da8-a036-af755b297ff2
-- title:
--   P2 M Ground Theory Heights  Heights Punctured Branch Same Order factor of punctured 43801c6296a6: P2 M Ground Theory Heights  Heights Punctured Branch Same Order factor of punctured 43801c6296a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Punctured Branch Same Order factor of punctured 43801c6296a6 construction uses the P2 M Ground Theory Heights  Heights Punctured Branch Same Order factor of punctured 43801c6296a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPuncturedBranchSameOrder.lean#L36-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPuncturedBranchSameOrder.lean#L36-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchSameOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCurveDiscInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPuncturedBranchSameOrder
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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder

theorem P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_factor_of_punctured_43801c6296a6 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {C D : ℂ → E} {ψ : ℂ → ℂ}
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hCd : DifferentiableOn ℂ C (Metric.ball 0 r)) (hCi : Set.InjOn C (Metric.ball 0 r))
    (hDd : DifferentiableOn ℂ D (Metric.ball 0 ρ)) (hDi : Set.InjOn D (Metric.ball 0 ρ)) (h0 : C 0 = D 0)
    (hψd : DifferentiableOn ℂ ψ (Metric.ball 0 ρ \ {0}))
    (hψ : ∀ τ ∈ Metric.ball (0 : ℂ) ρ \ {0}, ψ τ ∈ Metric.ball (0 : ℂ) r ∧ C (ψ τ) = D τ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, D τ = C (g τ)) ∧ 𝓝 0 ≤ map g (𝓝 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PuncturedBranchSameOrder».«factor_of_punctured» := P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_factor_of_punctured_43801c6296a6
