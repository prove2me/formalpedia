-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply
-- name    : QuaternionAlgebra.exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/ca74951e-af1d-5344-96b0-bfd764dc3c37
-- title:
--   Skolem–Noether for ℚ-embeddings of a quaternion algebra into M₂(K)
-- statement:
--   Let $a$ and $b$ be non-zero rational numbers and let $\mathbb{H}[\mathbb{Q},a,b]$ denote the associated rational quaternion algebra, generated over $\mathbb{Q}$ by elements $i,j$ with $i^2=a$, $j^2=b$ and $ij=-ji$. Let $K$ be a field of characteristic zero, and let $\iota_0,\iota_1 \colon \mathbb{H}[\mathbb{Q},a,b] \to M_2(K)$ be two homomorphisms of $\mathbb{Q}$-algebras into the algebra of $2\times 2$ matrices over $K$ (here $K$ is a $\mathbb{Q}$-algebra through its characteristic-zero structure). The assertion is that there exists $g \in \mathrm{GL}_2(K)$ such that for every $x \in \mathbb{H}[\mathbb{Q},a,b]$ one has $\iota_1(x) = g\,\iota_0(x)\,g^{-1}$, the products being taken in $M_2(K)$ with $g$ and $g^{-1}$ regarded as matrices via the coercion from the general linear group. No injectivity or non-degeneracy hypothesis beyond $a \neq 0$ and $b \neq 0$ is imposed on $\iota_0$ and $\iota_1$, and the conjugating element is a single $g$ serving all $x$ simultaneously.
--
--   This is the Skolem–Noether theorem in the shape needed for rational quaternion algebras: any two $\mathbb{Q}$-algebra maps of such an algebra into $2\times 2$ matrices over a field of characteristic zero differ by an inner automorphism. It is used in the construction of fake elliptic curves and of local conditions attached to maximal orders in quaternion algebras, where an identification of two given embeddings up to conjugation is required; the proof reduces to the corresponding statement for $K$-algebra endomorphisms of a matrix algebra, [`Matrix.exists_generalLinearGroup_forall_algHom_apply_eq_conj`](thm.html#Matrix.exists_generalLinearGroup_forall_algHom_apply_eq_conj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups

theorem QuaternionAlgebra.exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (K : Type) [Field K] [CharZero K]
    (ι₀ ι₁ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K) :
    ∃ g : GL (Fin 2) K, ∀ x : ℍ[ℚ, a, b],
      ι₁ x = (g : Matrix (Fin 2) (Fin 2) K) * ι₀ x * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by sorry
