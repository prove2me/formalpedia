-- Prove2me | Theorems.Thm_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
-- name    : Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/8b69796e-f5a5-5d5e-9b10-0f6ca14d891c
-- title:
--   Algebra homomorphisms to an algebraically closed field extend along module-finite extensions
-- statement:
--   Let $R$ be a commutative ring and $A$ a commutative $R$-algebra which is finite as an $R$-module, let $C$ be an $R$-subalgebra of $A$, and let $\Omega$ be an algebraically closed field equipped with an $R$-algebra structure. Then for every $R$-algebra homomorphism $h \colon C \to \Omega$ there exists an $R$-algebra homomorphism $\nu \colon A \to \Omega$ whose composite with the inclusion $C \hookrightarrow A$ (the coercion `C.val`) equals $h$; that is, $\nu$ restricts along the inclusion to $h$ on the nose, as an equality of $R$-algebra homomorphisms $C \to \Omega$. No hypothesis is imposed beyond the commutativity of $R$ and $A$, the module-finiteness of $A$ over $R$, and the assumption that $\Omega$ is an algebraically closed field over $R$; in particular $R$ need not be Noetherian or a field, $A$ need not be reduced or flat, and no compatibility between $h$ and the structure map $R \to \Omega$ other than $R$-linearity of $h$ is required. The universe levels of $R$, $A$ and $\Omega$ are independent.
--
--   This is the standard statement that a finite morphism of affine schemes is surjective on $\Omega$-points, i.e. lying over together with the extension of embeddings into an algebraically closed field. It is used in the construction of the connected–étale sequence for finite flat group schemes over $\mathbb{Z}_p$, in the study of Dieudonné modules attached to deformations, and in producing algebra homomorphisms out of local Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A]
    (C : Subalgebra R A) (Ω : Type w) [Field Ω] [Algebra R Ω] [IsAlgClosed Ω]
    (h : ↥C →ₐ[R] Ω) : ∃ ν : A →ₐ[R] Ω, ν.comp C.val = h := by sorry
