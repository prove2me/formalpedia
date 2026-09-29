-- Prove2me | Theorems.Thm_ValuationSubring_mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField
-- name    : ValuationSubring.mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/7682569b-0a82-5e5d-abe5-0498f3740238
-- title:
--   Pointwise fixing P∩ L^{D_P} forces membership in D_P
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra such that $L/K$ is Galois (the extension is not assumed finite), let $P$ be a valuation subring of $L$, and let $\tau$ be a $K$-algebra automorphism of $L$. Write $D_P =$ `P.decompositionSubgroup K` for the decomposition subgroup of $P$, that is, the stabiliser of $P$ in $L \simeq_{\mathrm{alg}[K]} L$ for the natural action of the Galois group on valuation subrings of $L$, and let $L^{D_P} =$ `IntermediateField.fixedField (P.decompositionSubgroup K)` be its fixed field, an intermediate field of $L/K$. The hypothesis is that $\tau$ fixes pointwise every element of $L$ lying simultaneously in $P$ and in $L^{D_P}$: for all $x \in L$, if $x \in P$ and $x \in L^{D_P}$ then $\tau(x) = x$. The conclusion is that $\tau$ belongs to $D_P$, i.e. $\tau \cdot P = P$ as valuation subrings of $L$. Thus fixing the ring $P \cap L^{D_P}$ pointwise already suffices, without assuming that $\tau$ fixes all of $L^{D_P}$.
--
--   This is the standard characterisation of the decomposition group as the Galois group over the decomposition field, in the form adapted to a possibly infinite Galois extension and with the hypothesis weakened to the decomposition ring $P \cap L^{D_P}$ rather than the whole decomposition field. It is used to recognise automorphisms of $\overline{\mathbb{Q}}$ that fix a decomposition ring as elements of the decomposition group, in the construction of the toric quotient of the $p$-divisible group attached to the finite part of a Néron model of a modular curve at $P$, and it is the engine of the variant phrased with the separable closure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (P : ValuationSubring L) (τ : L ≃ₐ[K] L)
    (h : ∀ x : L, x ∈ P → x ∈ IntermediateField.fixedField (P.decompositionSubgroup K) → τ x = x) :
    τ ∈ P.decompositionSubgroup K := by sorry
