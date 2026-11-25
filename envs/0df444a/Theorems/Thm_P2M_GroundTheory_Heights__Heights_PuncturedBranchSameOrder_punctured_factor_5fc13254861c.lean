-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_punctured_factor_5fc13254861c
-- name    : P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_punctured_factor_5fc13254861c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:13.608141+00:00
-- url     : https://prove2.me/theorems/93eed264-cb47-4358-b88e-9118dd766bdd
-- title:
--   P2 M Ground Theory Heights  Heights Punctured Branch Same Order punctured factor 5fc13254861c: P2 M Ground Theory Heights  Heights Punctured Branch Same Order punctured factor 5fc13254861c
-- statement:
--   The P2 M Ground Theory Heights  Heights Punctured Branch Same Order punctured factor 5fc13254861c construction uses the P2 M Ground Theory Heights  Heights Punctured Branch Same Order punctured factor 5fc13254861c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPuncturedBranchSameOrder.lean#L111-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPuncturedBranchSameOrder.lean#L111-L167

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

theorem P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_punctured_factor_5fc13254861c (hcut : PuncturedCurveDiscInverse.Statement) {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {q : Fin n → ℂ} (hI : IsRadicalAt I q) (hdim : ringKrullDim (curveLocalRing I q) = 1) (c d : VarBranch I 1 q)
    (ρ : ℝ) (hρ : 0 < ρ) (hcd : ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → d.toFun (fun _ ↦ τ) ∈ c.image) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, (d.toFun fun _ ↦ τ) = c.toFun fun _ ↦ g τ) ∧
      𝓝 0 ≤ map g (𝓝 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PuncturedBranchSameOrder».«punctured_factor» := P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_punctured_factor_5fc13254861c
