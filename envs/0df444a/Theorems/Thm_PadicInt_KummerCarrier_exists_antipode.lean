-- Prove2me | Theorems.Thm_PadicInt_KummerCarrier_exists_antipode
-- name    : PadicInt.KummerCarrier.exists_antipode
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/c2f70cdf-8302-526d-b3fa-6650e7bc9c38
-- title:
--   Existence of an antipode on the Kummer carrier
-- statement:
--   Let $p$ be a natural number assumed prime and let $u$ be a unit of $\mathbb{Z}_p$. Write $H =$ `Carrier p u` for the dependent product $\prod_{j \in \mathbb{Z}/p} A\,p\,u\,j$ of the $\mathbb{Z}_p$-algebras `A p u j` indexed by the residues $j$ modulo $p$, equipped with its comultiplication `Δ p u` and counit `ε p u` (algebra homomorphisms $H \to H \otimes_{\mathbb{Z}_p} H$ and $H \to \mathbb{Z}_p$ defined in the module, here used through their underlying $\mathbb{Z}_p$-linear maps). The assertion is that there exists a $\mathbb{Z}_p$-linear endomorphism $S$ of $H$ satisfying both convolution identities
--   $$\mathrm{mul} \circ (S \otimes \mathrm{id}_H) \circ \Delta = \eta \circ \varepsilon, \qquad \mathrm{mul} \circ (\mathrm{id}_H \otimes S) \circ \Delta = \eta \circ \varepsilon,$$
--   as equalities of linear maps $H \to H$, where $\mathrm{mul}$ is the multiplication map `LinearMap.mul'` on $H$ and $\eta =$ `Algebra.linearMap` is the structure map $\mathbb{Z}_p \to H$. Thus $S$ is a two-sided convolution inverse of the identity; only its existence is asserted, no formula for $S$ being recorded in the statement.
--
--   These are exactly the two antipode axioms required, alongside the bialgebra axioms, to equip the Kummer carrier with a Hopf algebra structure over $\mathbb{Z}_p$; classically $S$ implements inversion on the associated Kummer group scheme. It is used by [`PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval`](thm.html#PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval) in the construction of the finite flat Hopf algebras of Oort–Tate type attached to the unit $u$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_KummerCarrier_exists_antipode.lean

import Mathlib
import Definitions.Def_PadicInt_KummerCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in
open PadicInt.KummerCarrier in

theorem PadicInt.KummerCarrier.exists_antipode (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    ∃ S : Carrier p u →ₗ[ℤ_[p]] Carrier p u,
      (LinearMap.mul' ℤ_[p] (Carrier p u) ∘ₗ S.rTensor (Carrier p u) ∘ₗ (Δ p u).toLinearMap
        = Algebra.linearMap ℤ_[p] (Carrier p u) ∘ₗ (ε p u).toLinearMap) ∧
      (LinearMap.mul' ℤ_[p] (Carrier p u) ∘ₗ S.lTensor (Carrier p u) ∘ₗ (Δ p u).toLinearMap
        = Algebra.linearMap ℤ_[p] (Carrier p u) ∘ₗ (ε p u).toLinearMap) := by sorry
