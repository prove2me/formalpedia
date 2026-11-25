-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_span_fibreVec_eq_top_3f80ac305458
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_span_fibreVec_eq_top_3f80ac305458
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:01.230226+00:00
-- url     : https://prove2.me/theorems/8448cc4d-91e4-5968-b613-c2ae2c57058b
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas span fibre Vec eq top 3f80ac305458: P2 M Ground Theory Heights  Heights Lattice Lemmas span fibre Vec eq top 3f80ac305458
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas span fibre Vec eq top 3f80ac305458 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas span fibre Vec eq top 3f80ac305458 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PDiagonalChange.lean#L15-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PDiagonalChange.lean#L15-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_span_fibreVec_eq_top_3f80ac305458 (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«span_fibreVec_eq_top» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_span_fibreVec_eq_top_3f80ac305458
