-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_linSubst_linForm_d475c9bb2ba4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_linSubst_linForm_d475c9bb2ba4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:41.250654+00:00
-- url     : https://prove2.me/theorems/1ce28dae-5847-4482-a0dd-668622c90568
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter lin Subst lin Form d475c9bb2ba4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter lin Subst lin Form d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter lin Subst lin Form d475c9bb2ba4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter lin Subst lin Form d475c9bb2ba4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L31-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {Φ : Type} [Field Φ] {σ : Type} [Fintype σ] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_linSubst_linForm_d475c9bb2ba4 (ℓ : σ → Fin n → Φ) (μ : σ → Φ) :
    linSubst ℓ (∑ q, C (μ q) * X q) = ∑ b, C (∑ q, μ q * ℓ q b) * X b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«linSubst_linForm» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_linSubst_linForm_d475c9bb2ba4
