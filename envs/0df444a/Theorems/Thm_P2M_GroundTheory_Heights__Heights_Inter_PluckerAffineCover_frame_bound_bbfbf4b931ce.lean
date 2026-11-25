-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_bound_bbfbf4b931ce
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_bound_bbfbf4b931ce
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:28.468228+00:00
-- url     : https://prove2.me/theorems/e9f5a91f-2413-4b7f-b184-523c9f5c9af9
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover frame bound bbfbf4b931ce: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover frame bound bbfbf4b931ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover frame bound bbfbf4b931ce construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover frame bound bbfbf4b931ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L74-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L74-L149

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)
variable {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_bound_bbfbf4b931ce (B : ChartBundle ℤ x r E) {K : ℕ} (f c : Fin K → Ω) (hf : ∀ l, f l ∈ chartRing ℤ x i)
    (hc : ∀ l, c l ∈ chartRing ℤ x i) (hs : ∑ l, c l * f l = 1) (bb : Fin K → Fin r → E)
    (hli : ∀ l, LinearIndependent Ω (bb l)) (hsp : ∀ l, Submodule.span Ω (Set.range (bb l)) = ⊤)
    (hloc : ∀ l e, (∃ n : ℕ, f l ^ n • e ∈ B.lat i) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing ℤ x i) ∧ e = ∑ q, a q • bb l q)
    (l : Fin K) :
    ∃ M : ℕ, ∀ v ∈ B.lat i, ∀ q,
      f l ^ M * (Module.Basis.mk (hli l) (hsp l).ge).repr v q ∈ chartRing ℤ x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«frame_bound» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_bound_bbfbf4b931ce
