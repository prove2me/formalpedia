-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_gen_572f531e0883
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_gen_572f531e0883
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:50.399502+00:00
-- url     : https://prove2.me/theorems/3fab6de1-b935-4c77-9a1b-fb29689bdb56
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover frame gen 572f531e0883: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover frame gen 572f531e0883
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover frame gen 572f531e0883 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover frame gen 572f531e0883 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L63-L72

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_gen_572f531e0883 (B : ChartBundle ℤ x r E) {f : Ω} (bb : Fin r → E)
    (hloc : ∀ e, (∃ n : ℕ, f ^ n • e ∈ B.lat i) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ chartRing ℤ x i) ∧ e = ∑ q, a q • bb q) (q : Fin r) :
    ∃ n : ℕ, f ^ n • bb q ∈ B.lat i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«frame_gen» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_gen_572f531e0883
