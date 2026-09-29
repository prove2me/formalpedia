-- Prove2me | Theorems.Thm_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois
-- name    : ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/ac213ab1-7acf-5e22-b789-17b6e9150742
-- title:
--   Transitivity of the Galois group on valuation rings over O
-- statement:
--   Let $E$ and $F$ be fields with $F$ an $E$-algebra that is finite-dimensional over $E$ and Galois, let $O$ be a valuation subring of $E$, and let $O'$ and $O''$ be valuation subrings of $F$, each assumed to lie over $O$ in the sense that for every $x \in E$ the image $\mathrm{algebraMap}_{E,F}(x)$ lies in $O'$ (respectively in $O''$) if and only if $x$ lies in $O$. The conclusion is the existence of an $E$-algebra automorphism $\sigma$ of $F$ such that for every $x \in F$ one has $\sigma(x) \in O''$ if and only if $x \in O'$; that is, $\sigma$ carries $O'$ onto $O''$. The conclusion is stated elementwise, without reference to the pointwise action of the Galois group on valuation subrings, and asserts only existence of one such $\sigma$, not any description of the stabiliser or of the set of all such automorphisms.
--
--   This is the classical conjugacy theorem for the extensions of a valuation to a finite Galois extension: the Galois group acts transitively on the valuation subrings of $F$ lying over a given valuation subring of $E$. It is used to derive the corresponding statement for infinite Galois extensions in [`ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois_infinite`](thm.html#ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois_infinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois.lean

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.Galois.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [FiniteDimensional E F]
    [IsGalois E F]
    (O : ValuationSubring E)
    (O' O'' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) :
    ∃ σ : F ≃ₐ[E] F, ∀ x : F, σ x ∈ O'' ↔ x ∈ O' := by sorry
