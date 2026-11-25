-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_hypotheses_inhabited_1185a6575806
-- name    : P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_hypotheses_inhabited_1185a6575806
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:25.029797+00:00
-- url     : https://prove2.me/theorems/f31ea2fd-4f77-431e-97ae-ad2871580a4c
-- title:
--   P2 M Ground Theory Heights  Heights Model Prime Opens Cover hypotheses inhabited 1185a6575806: P2 M Ground Theory Heights  Heights Model Prime Opens Cover hypotheses inhabited 1185a6575806
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Prime Opens Cover hypotheses inhabited 1185a6575806 construction uses the P2 M Ground Theory Heights  Heights Model Prime Opens Cover hypotheses inhabited 1185a6575806 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L533-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L533-L555

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_hypotheses_inhabited_1185a6575806 :
    (∀ p ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes),
      ¬ ((p : ℕ) : ℤ) ∣ (if (p : ℕ) = 2 then 3 else 2)) ∧
    (∀ p ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes),
      ∀ q ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes), q ≠ p →
        ((q : ℕ) : ℤ) ∣ (if (p : ℕ) = 2 then 3 else 2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«PrimeOpensCover».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_PrimeOpensCover_hypotheses_inhabited_1185a6575806
