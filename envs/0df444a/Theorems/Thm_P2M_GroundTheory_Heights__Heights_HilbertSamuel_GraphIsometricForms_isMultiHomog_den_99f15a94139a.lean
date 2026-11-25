-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_isMultiHomog_den_99f15a94139a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_isMultiHomog_den_99f15a94139a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:52.973841+00:00
-- url     : https://prove2.me/theorems/d455d3dc-81ad-4981-bb50-7c3b2a99b64c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms is Multi Homog den 99f15a94139a: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms is Multi Homog den 99
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms is Multi Homog den 99f15a94139a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms is Multi Homog den 99f15a94139a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L96-L102

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_isMultiHomog_den_b8412c92fdca

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_isMultiHomog_den_99f15a94139a [DecidableEq K] [DecidableEq K₂] {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) :
    IsMultiHomog (den g j a)
      (∑ k, ((a k).toNat • Pi.single (Sum.inr k) 1 + (-a k).toNat • Function.extend Sum.inl (δ k) 0)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometricForms».«isMultiHomog_den» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_isMultiHomog_den_99f15a94139a
