-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ReducedBasisBound_short_basis_433a14dbcd30
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ReducedBasisBound_short_basis_433a14dbcd30
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:15.730936+00:00
-- url     : https://prove2.me/theorems/3294ad61-d884-421e-971f-a0bdc6c29981
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Reduced Basis Bound short basis 433a14dbcd30: P2 M Ground Theory Heights  Heights Finite Covolume Reduced Basis Bound short basis 433a14dbcd30
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Reduced Basis Bound short basis 433a14dbcd30 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Reduced Basis Bound short basis 433a14dbcd30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PReducedBasisBound.lean#L12-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PReducedBasisBound.lean#L12-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StReducedBasisBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PReducedBasisBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Module Submodule Matrix GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ReducedBasisBound_short_basis_433a14dbcd30 {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (m : ℕ) : ∀ lam : ℝ, 0 < lam → ∀ C : ℝ, ∃ R : ℝ,
    ∀ b : Fin m → W, LinearIndependent ℝ b → Sep (span ℤ (Set.range b)) lam →
      (gram ℝ b).det ≤ C → ∃ b' : Fin m → W, span ℤ (Set.range b') = span ℤ (Set.range b) ∧
        ∀ i, ‖b' i‖ ≤ R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ReducedBasisBound».«short_basis» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ReducedBasisBound_short_basis_433a14dbcd30
