-- Prove2me | Theorems.Thm_Subring_exists_injective_ringHom_isDiscreteValuationRing_of_module_finite
-- name    : Subring.exists_injective_ringHom_isDiscreteValuationRing_of_module_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/60a60c4d-844b-5490-bf8c-587bc180904c
-- title:
--   Orders in ℂ embed into complete DVRs above ℓ
-- statement:
--   Let $A$ be a subring of $\mathbb{C}$ which is finitely generated as a $\mathbb{Z}$-module, and let $l$ be a prime natural number. Then there exists a ring $\mathcal{O}'$ (in the lowest universe), equipped with a commutative ring structure, which is a domain, a discrete valuation ring, complete with respect to the adic filtration of its maximal ideal (`IsAdicComplete` for `IsLocalRing.maximalIdeal`), has finite residue field, and has characteristic zero, such that two conditions hold: the image of $l$ under the canonical map $\mathbb{N} \to \mathcal{O}'$ lies in the maximal ideal of $\mathcal{O}'$, and there is a ring homomorphism $\iota : A \to \mathcal{O}'$ which is injective. All the structure on $\mathcal{O}'$ is existentially quantified together with the two properties, so the statement asserts only the existence of such a coefficient ring together with an embedding of $A$ into it; no compatibility with the inclusion $A \subseteq \mathbb{C}$, and no minimality or uniqueness of $\mathcal{O}'$, is asserted.
--
--   Classically $\mathcal{O}'$ is the valuation ring of the completion of the fraction field of the order $A$ at a prime above $\ell$; the statement packages this as the existence of a complete discrete valuation ring of characteristic zero with finite residue field in which $\ell$ is not a unit and which receives the given order. It is used to place the coefficients of a newform into a coefficient ring of the shape required by the Galois representations occurring in the modularity assembly, where it is cited by the construction of a modular model of the relevant conductor level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subring_exists_injective_ringHom_isDiscreteValuationRing_of_module_finite.lean

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Finiteness.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Subring.exists_injective_ringHom_isDiscreteValuationRing_of_module_finite (A : Subring ℂ) [Module.Finite ℤ A] (l : ℕ) [Fact l.Prime] :
    ∃ (𝓞' : Type) (_ : CommRing 𝓞') (_ : IsDomain 𝓞') (_ : IsDiscreteValuationRing 𝓞')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝓞') 𝓞') (_ : Finite (IsLocalRing.ResidueField 𝓞'))
      (_ : CharZero 𝓞'),
      (l : 𝓞') ∈ IsLocalRing.maximalIdeal 𝓞' ∧ ∃ ι : A →+* 𝓞', Function.Injective ι := by sorry
