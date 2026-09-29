-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod
-- name    : QuaternionAlgebra.IsOrder.surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/643d5dc9-56a0-5fcf-9343-e15e977cf2e8
-- title:
--   Rigidity of unital multiplicative maps from an order to M₂(ℤ/N)
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project predicate [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11): $1\in\Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is all of $\mathbb{H}[\mathbb{Q},a,b]$, and $\Lambda$ is finitely generated over $\mathbb{Z}$. Let $N$ be a nonzero natural number and let $\varphi,\psi:\Lambda\to M_2(\mathbb{Z}/N)$ be $\mathbb{Z}$-linear maps. Assume of each of them that it sends the element $1$ of $\Lambda$ to the identity matrix and that it is multiplicative, i.e. $\varphi(xy)=\varphi(x)\varphi(y)$ and $\psi(xy)=\psi(x)\psi(y)$ for all $x,y\in\Lambda$ (the product $xy$ being taken in $\Lambda$ via the given membership proof). Assume further that $\varphi$ is surjective and that for every $x\in\Lambda$ one has $\varphi(x)=0$ if and only if $x=N\cdot y$ in $\mathbb{H}[\mathbb{Q},a,b]$ for some $y\in\Lambda$. The conclusion is that $\psi$ is then likewise surjective and that for every $x\in\Lambda$, $\psi(x)=0$ if and only if $x=N\cdot y$ for some $y\in\Lambda$; that is, $\psi$ has the same image and the same kernel $N\Lambda$ as $\varphi$. The proof uses only the clauses $1\in\Lambda$ and closure under multiplication of the order hypothesis, not the span or finite-generation clauses.
--
--   This is a rigidity statement for reductions of an order modulo $N$: any unital multiplicative $\mathbb{Z}$-linear map from $\Lambda$ to $M_2(\mathbb{Z}/N)$ is forced to be the reduction $\Lambda\to\Lambda/N\Lambda\cong M_2(\mathbb{Z}/N)$ up to an automorphism, once one such identification is known to exist. It is used in the construction attached to maximal orders in the Čerednik–Drinfel'd setting, in [`CerednikDrinfeld.QM.exists_equiv_torsion_and_forall_pushPt_eq_mulVec_of_forall_exists_eq_of_isMaximalOrder`](thm.html#CerednikDrinfeld.QM.exists_equiv_torsion_and_forall_pushPt_eq_mulVec_of_forall_exists_eq_of_isMaximalOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod.lean

import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (N : ℕ) [NeZero N]
    (φ ψ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N))
    (hφ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b]))
    (hψ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ψ ⟨1, h⟩ = 1)
    (hψmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ψ x * ψ y) :
    Function.Surjective ψ ∧
      ∀ x : ↥Λ, ψ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b]) := by sorry
