-- Prove2me | Theorems.Thm_ValuationSubring_exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois
-- name    : ValuationSubring.exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/9431d30d-ef23-51dd-94e7-72be0b551e3d
-- title:
--   Galois conjugacy of valuation subrings over a common restriction
-- statement:
--   Let $E$ and $F$ be fields with $F$ an algebra over $E$ that is finite-dimensional and Galois over $E$, and let $O_1, O_2$ be valuation subrings of $F$. Assume that $O_1$ and $O_2$ cut out the same subset of $E$, in the sense that for every $x \in E$ one has $\mathrm{algebraMap}_{E,F}(x) \in O_1$ if and only if $\mathrm{algebraMap}_{E,F}(x) \in O_2$. The conclusion is that there exists an $E$-algebra automorphism $\sigma$ of $F$ with $\sigma \bullet O_1 = O_2$, the action being the pointwise (scoped `Pointwise`) action of automorphisms on valuation subrings, so that $x \in \sigma \bullet O_1$ holds precisely when $\sigma^{-1}(x) \in O_1$. Equivalently, $\sigma(O_1) = O_2$ as subrings of $F$. No separability or normality hypothesis beyond `IsGalois E F` is imposed, and no assumption is made on the residue characteristic or on the value groups.
--
--   This is the classical conjugation theorem for valuations: the Galois group of a finite Galois extension $F/E$ acts transitively on the valuation rings of $F$ prolonging a given valuation ring of $E$. In this development it is used in the study of Igusa rings attached to modular curves of full level, where a valuation subring characterised by its restriction to the base field must be exhibited as a Galois conjugate of a specified one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois
    {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
    (O₁ O₂ : ValuationSubring F)
    (h : ∀ x : E, algebraMap E F x ∈ O₁ ↔ algebraMap E F x ∈ O₂) :
    ∃ σ : F ≃ₐ[E] F, σ • O₁ = O₂ := by sorry
