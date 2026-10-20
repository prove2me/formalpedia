-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_physical_necessary
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.physical_necessary
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:26:55.899235+00:00
-- url     : https://prove2.me/theorems/044eba0d-ab6d-4d9e-8e44-db63194c31ee
-- title:
--   Necessary conditions for physical events in any OPT
-- statement:
--   Let $\mathcal T$ be an operational probabilistic theory with systems, a trivial system $I$, sequential and parallel composition, identities, allowed tests, and coarse-graining. Physical events belong to allowed tests; deterministic events are singleton tests. States are events from $I$, effects are events to $I$, and $\mathrm{St}_+(A)$ is the finite conical hull of states of $A$. Let $F\in\mathrm{Transf}_{\mathbb R}(A,B)$ be a candidate in the real span of events, with its ambient ancillary action. No finite-dimensionality, local tomography, or physicality of $F$ is assumed. If $F$ is physical, then
--
--   $$ (F\otimes I_S)\rho\in\mathrm{St}_+(BS)\quad\text{for every }S\text{ and every }\rho\in\mathrm{St}(AS),$$
--
--   and the ancillary normalization bound holds: every deterministic ancillary input state and deterministic output effect gives a scalar at most one. States in the first assertion include subnormalized events. This supplies necessary conditions for physicality in arbitrary theories; it asserts no sufficiency.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 23, Theorem F.10

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v

section OperationalDefinitions

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℝ C]

variable [MonoidalCategory C] [SymmetricCategory C]

variable [MonoidalPreadditive C] [MonoidalLinear ℝ C]

/-- PDF pp.22–23, Theorem F.10: physicality implies cone preservation on
ancillary physical states and the deterministic-state/effect upper bound.
Necessity only in an arbitrary OPT, not an unrestricted-theory iff. -/
theorem physical_necessary (T : OperationalTheory C) {A B : C} (f : A ⟶ B)
    (hf : IsPhysical T f) :
    (∀ S : C, ∀ rho : (𝟙_ C) ⟶ (A ⊗ S), IsPhysical T rho →
      InStateCone T (B ⊗ S) (rho ≫ (f ⊗ₘ 𝟙 S))) ∧ CompleteUpperBound T f := by sorry

end OperationalDefinitions

end QAlgorithms.Papers.Independent.Dependency50.P06

end
