-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_log_gramDet_le_e183ddd6b300
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_log_gramDet_le_e183ddd6b300
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:09.187704+00:00
-- url     : https://prove2.me/theorems/06c67a7f-98c0-4533-9d60-c33cfd8aecb1
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas log gram Det le e183ddd6b300: P2 M Ground Theory Heights  Heights Lattice Lemmas log gram Det le e183ddd6b300
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas log gram Det le e183ddd6b300 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas log gram Det le e183ddd6b300 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamard.lean#L47-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamard.lean#L47-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamard
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
open GroundTheory.Heights₂.Heights InnerProductSpace
universe u v w
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_log_gramDet_le_e183ddd6b300 (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s) :
    Real.log (gramDet h σ s) ≤ 2 * ∑ i, Real.log ‖fibreVec h σ (s i)‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«log_gramDet_le» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_log_gramDet_le_e183ddd6b300
