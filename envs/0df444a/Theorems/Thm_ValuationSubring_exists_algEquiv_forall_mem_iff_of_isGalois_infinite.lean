-- Prove2me | Theorems.Thm_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois_infinite
-- name    : ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois_infinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/f628b9aa-62c2-544b-bb0b-6a6d8da6711d
-- title:
--   Transitivity on valuation rings in an infinite Galois extension
-- statement:
--   Let $E$ and $F$ be fields with $F$ an $E$-algebra such that $F/E$ is Galois (no finiteness is assumed). Let $O$ be a valuation subring of $E$, and let $O'$ and $O''$ be valuation subrings of $F$, both lying over $O$ in the sense that for every $x \in E$ one has $\mathrm{algebraMap}\,x \in O'$ if and only if $x \in O$, and likewise $\mathrm{algebraMap}\,x \in O''$ if and only if $x \in O$. The conclusion asserts the existence of an $E$-algebra automorphism $\sigma$ of $F$ such that for every $x \in F$ one has $\sigma x \in O''$ if and only if $x \in O'$; that is, $\sigma$ carries $O'$ onto $O''$ as sets, the membership equivalence being stated pointwise rather than as an equality of subrings.
--
--   This is the conjugacy of prolongations of a valuation in Hilbert ramification theory, in its form for an arbitrary, possibly infinite, Galois extension: $\mathrm{Gal}(F/E)$ acts transitively on the valuation rings of $F$ lying over a fixed valuation ring of $E$. It is used in the project to compare places above a given place, for instance in the study of inertia at places of number fields and of the integral models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois_infinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois_infinite
    {E F : Type*} [Field E] [Field F] [Algebra E F] [IsGalois E F]
    (O : ValuationSubring E)
    (O' O'' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) :
    ∃ σ : F ≃ₐ[E] F, ∀ x : F, σ x ∈ O'' ↔ x ∈ O' := by sorry
