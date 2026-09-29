-- Prove2me | Theorems.Thm_Subring_exists_injective_ringHom_isDiscreteValuationRing_map_mem_maximalIdeal_of_module_finite
-- name    : Subring.exists_injective_ringHom_isDiscreteValuationRing_map_mem_maximalIdeal_of_module_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/77a0d191-c045-5482-887f-a6f42891872f
-- title:
--   Orders in ℂ embed into complete DVRs respecting a prime above l
-- statement:
--   Let $A$ be a subring of $\mathbb{C}$ which is finite as a $\mathbb{Z}$-module, let $l$ be a prime number, and let $\mathfrak{m}_A$ be a prime ideal of $A$ with $l \in \mathfrak{m}_A$ (i.e. the image of $l$ under the canonical map $\mathbb{Z} \to A$ lies in $\mathfrak{m}_A$). The assertion is the existence of a type $\mathcal{O}'$ in the lowest universe, together with the structure of a commutative ring on it which is an integral domain, is a discrete valuation ring, is adically complete with respect to its maximal ideal, has finite residue field and has characteristic zero, such that the image of $l$ lies in the maximal ideal of $\mathcal{O}'$, and such that there is a ring homomorphism $\iota : A \to \mathcal{O}'$ which is injective and satisfies $\iota(x) \in \mathfrak{m}_{\mathcal{O}'}$ for every $x \in \mathfrak{m}_A$. Only the inclusion $\iota(\mathfrak{m}_A) \subseteq \mathfrak{m}_{\mathcal{O}'}$ is asserted, not that $\mathfrak{m}_A$ is the full contraction of $\mathfrak{m}_{\mathcal{O}'}$.
--
--   This is the standard statement that an order $A$ in a number field admits a place above $l$ extending a prescribed prime $\mathfrak{m}_A \ni l$: one completes the integral closure of $A$ in $A \otimes \mathbb{Q}$ at a prime lying over $\mathfrak{m}_A$, obtaining a complete discrete valuation ring of characteristic zero with finite residue field. It is used to pass from the Hecke eigenvalue ring of a newform, realised inside $\mathbb{C}$, to coefficients in a complete local ring of residue characteristic $l$, in the construction of normalised eigenforms of lowered level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subring_exists_injective_ringHom_isDiscreteValuationRing_map_mem_maximalIdeal_of_module_finite.lean

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Finiteness.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Subring.exists_injective_ringHom_isDiscreteValuationRing_map_mem_maximalIdeal_of_module_finite
    (A : Subring ℂ) [Module.Finite ℤ A] (l : ℕ) [Fact l.Prime]
    (𝔪A : Ideal A) [𝔪A.IsPrime] (hl : (l : A) ∈ 𝔪A) :
    ∃ (𝓞' : Type) (_ : CommRing 𝓞') (_ : IsDomain 𝓞') (_ : IsDiscreteValuationRing 𝓞')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝓞') 𝓞')
      (_ : Finite (IsLocalRing.ResidueField 𝓞')) (_ : CharZero 𝓞'),
      (l : 𝓞') ∈ IsLocalRing.maximalIdeal 𝓞' ∧
        ∃ ι : A →+* 𝓞', Function.Injective ι ∧
          ∀ x : A, x ∈ 𝔪A → ι x ∈ IsLocalRing.maximalIdeal 𝓞' := by sorry
