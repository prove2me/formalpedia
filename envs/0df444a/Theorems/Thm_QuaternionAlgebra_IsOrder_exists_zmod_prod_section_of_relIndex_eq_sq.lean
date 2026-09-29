-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_exists_zmod_prod_section_of_relIndex_eq_sq
-- name    : QuaternionAlgebra.IsOrder.exists_zmod_prod_section_of_relIndex_eq_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/875d2671-2bf5-5bd3-bcb3-437b8f22b8f4
-- title:
--   A line L₀ with ℓΛ⊆ L₀⊆Λ admits (ℤ/ℓ)² representatives
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project predicate `IsOrder`: $1\in\Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is the whole algebra, and $\Lambda$ is finitely generated over $\mathbb{Z}$. Let $\ell$ be a prime and let $L_0$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ with $L_0\subseteq\Lambda$, such that $\ell x\in L_0$ for every $x\in\Lambda$, and such that the relative index of the additive subgroup underlying $L_0$ in that underlying $\Lambda$ equals $\ell^2$. The conclusion produces a map $\rho:\mathbb{Z}/\ell\times\mathbb{Z}/\ell\to\Lambda$ with four properties: every value $\rho(v)$ lies in $L_0$; for all $v,w$ there is $y\in\Lambda$ with $\rho(v+w)-\rho(v)-\rho(w)=\ell y$; every $x\in\Lambda$ lying in $L_0$ satisfies $x-\rho(v)=\ell y$ for some $v$ and some $y\in\Lambda$; and if $\rho(v)-\rho(w)=\ell y$ for some $y\in\Lambda$ then $v=w$. Thus $\rho$ is a set-theoretic system of representatives for $L_0$ modulo $\ell\Lambda$, additive modulo $\ell\Lambda$, with congruence modulo $\ell\Lambda$ expressed throughout as divisibility by $\ell$ inside $\Lambda$.
--
--   This records that a subgroup $L_0$ with $\ell\Lambda\subseteq L_0\subseteq\Lambda$ of index $\ell^2$ has $L_0/\ell\Lambda$ an $\mathbb{F}_\ell$-plane, in the concrete form of explicit representatives indexed by $(\mathbb{Z}/\ell)^2$, so that consumers may work with honest elements of the order. It is used in the Čerednik–Drinfeld fake elliptic curve material, where full level structures are twisted by such representatives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_exists_zmod_prod_section_of_relIndex_eq_sq.lean

import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open QuaternionAlgebra
open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_zmod_prod_section_of_relIndex_eq_sq
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2) :
    ∃ ρ : ZMod ℓ × ZMod ℓ → ↥Λ,
      (∀ v, ((ρ v : ↥Λ) : ℍ[ℚ, a, b]) ∈ L₀) ∧
      (∀ v w, ∃ y : ↥Λ,
        ((ρ (v + w) : ↥Λ) : ℍ[ℚ, a, b]) - (ρ v : ℍ[ℚ, a, b]) - (ρ w : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        ∃ v, ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) - (ρ v : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ v w, (∃ y : ↥Λ, ((ρ v : ↥Λ) : ℍ[ℚ, a, b]) - (ρ w : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) → v = w) := by sorry
