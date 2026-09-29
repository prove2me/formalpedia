-- Prove2me | Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
-- name    : ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/9bf499d9-e7bc-5c04-8d7a-a47afb67bc9c
-- title:
--   Reduction into characteristic q has kernel mathfrak m_A
-- statement:
--   Let $A$ be a valuation subring of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ (so $A$ is a local ring with maximal ideal `IsLocalRing.maximalIdeal A`), let $k$ be a field, let $q$ be a prime number, and suppose $k$ has characteristic $q$. Let $\mathrm{red} \colon A \to k$ be a ring homomorphism, and let $c \in A$. Then $\mathrm{red}(c) = 0$ if and only if $c$ lies in the maximal ideal of $A$. Equivalently, the kernel of any ring homomorphism from $A$ to a field of prime characteristic is exactly $\mathfrak m_A$; in particular such a homomorphism is automatically a reduction map in the sense of places, and no further compatibility between $\mathrm{red}$ and the valuation is assumed.
--
--   This is the statement that a valuation ring of $\overline{\mathbb Q}$ has rank one, in the form needed to identify the kernel of a reduction map into characteristic $q$ with the maximal ideal. It is used throughout the construction of characteristic-$q$ models of modular curves and in the analysis of prolongations of places, for instance in [`ModularCurve.CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem`](thm.html#ModularCurve.CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem) and in [`ModularCurve.PlaceSpecialization.ProlongationTuple.card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
    (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (red : A →+* k) (c : A) :
    red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := by sorry
