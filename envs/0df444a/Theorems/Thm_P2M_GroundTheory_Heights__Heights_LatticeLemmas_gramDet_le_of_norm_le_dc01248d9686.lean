-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_le_of_norm_le_dc01248d9686
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_le_of_norm_le_dc01248d9686
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:43.688799+00:00
-- url     : https://prove2.me/theorems/681663f6-9a94-5dee-bb96-d563eba50af7
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det le of norm le dc01248d9686: P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det le of norm le dc01248d9686
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det le of norm le dc01248d9686 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det le of norm le dc01248d9686 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PNormComparison.lean#L68-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PNormComparison.lean#L68-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PNormComparison
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
open scoped ComplexOrder MatrixOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_le_of_norm_le_dc01248d9686 {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h h' : HermitianMetric K E) (σ : K →+* ℂ) (A : ℝ)
    (hA : ∀ x : Fibre σ E, ‖FibreSpace.equiv h' σ x‖ ≤ A * ‖FibreSpace.equiv h σ x‖)
    {r : ℕ} {s : Fin r → E} (hs : LinearIndependent (𝓞 K) s) :
    gramDet h' σ s ≤ (max A 0 ^ 2) ^ r * gramDet h σ s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«gramDet_le_of_norm_le» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_le_of_norm_le_dc01248d9686
