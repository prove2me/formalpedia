-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mem_iff_forall_mulVec_mem
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mem_iff_forall_mulVec_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/da00c1d1-9050-51df-864e-29980afbd9f9
-- title:
--   Rank-two right 𝒪-lattices in H² are free
-- statement:
--   Let $c,d\in\mathbb Q$ and let $q$ be a prime, and suppose the quaternion algebra $\mathbb H[\mathbb Q,c,d]$ satisfies `IsDefiniteRamifiedExactlyAt c d q`, that is: $c<0$, $d<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb Q$ the completed algebra $\mathbb H[\mathbb Q,c,d]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra (every nonzero element is a unit) exactly when $q$ lies in $v$. Let $O$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,c,d]$ which is a maximal order, i.e. $O$ contains $1$, is closed under multiplication, spans the algebra over $\mathbb Q$, is finitely generated over $\mathbb Z$, and every order containing $O$ equals $O$. Let $M$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,c,d]^2$ (indexed by `Fin 2`) which is finitely generated, spans $\mathbb H[\mathbb Q,c,d]^2$ over $\mathbb Q$, and is stable under coordinatewise right multiplication by elements of $O$. Then there exist matrices $\gamma,\gamma'\in M_2(\mathbb H[\mathbb Q,c,d])$ with $\gamma\gamma'=1$ and $\gamma'\gamma=1$ such that for every $x\in\mathbb H[\mathbb Q,c,d]^2$ one has $x\in M$ if and only if every coordinate of $\gamma'x$ lies in $O$; equivalently $M=\gamma O^2$.
--
--   This is the statement that the class number of the maximal order $M_2(O)$ in $M_2(H)$ is one: every full right $O$-stable lattice of rank two is free, with basis the columns of an invertible $\gamma$. It is used in the construction of injective maps from orders into matrix algebras over $H$ with prescribed integrality, in particular by [`QuaternionAlgebra.exists_algHom_matrix_injective_forall_apply_mem_of_isOrder_of_isMaximalOrder`](thm.html#QuaternionAlgebra.exists_algHom_matrix_injective_forall_apply_mem_of_isOrder_of_isMaximalOrder) and its variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mem_iff_forall_mulVec_mem.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mem_iff_forall_mulVec_mem
    {c d : ℚ} (q : ℕ) [Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (M : Submodule ℤ (Fin 2 → ℍ[ℚ, c, d])) (hfg : M.FG)
    (hspan : Submodule.span ℚ (M : Set (Fin 2 → ℍ[ℚ, c, d])) = ⊤)
    (hM : ∀ m ∈ M, ∀ o ∈ O, (fun i => m i * o) ∈ M) :
    ∃ γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], γ * γ' = 1 ∧ γ' * γ = 1 ∧
      ∀ x : Fin 2 → ℍ[ℚ, c, d], x ∈ M ↔ ∀ i, (γ'.mulVec x) i ∈ O := by sorry
