-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_eq_of_norm_eq_284c59650304
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_eq_of_norm_eq_284c59650304
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:53.695431+00:00
-- url     : https://prove2.me/theorems/03815aae-352a-4cf0-ae32-68751517f38d
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det eq of norm eq 284c59650304: P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det eq of norm eq 284c59650304
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det eq of norm eq 284c59650304 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det eq of norm eq 284c59650304 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PDiagonalChange.lean#L52-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PDiagonalChange.lean#L52-L98

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

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_eq_of_norm_eq_284c59650304 (h h' : HermitianMetric K E) (σ : K →+* ℂ)
    (T : Fibre σ E →ₗ[ℂ] Fibre σ E)
    (hT : ∀ x, ‖FibreSpace.equiv h' σ x‖ = ‖FibreSpace.equiv h σ (T x)‖) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    gramDet h' σ s = ‖LinearMap.det T‖ ^ 2 * gramDet h σ s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«gramDet_eq_of_norm_eq» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_eq_of_norm_eq_284c59650304
