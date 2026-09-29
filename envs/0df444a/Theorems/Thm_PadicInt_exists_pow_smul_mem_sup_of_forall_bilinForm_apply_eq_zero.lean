-- Prove2me | Theorems.Thm_PadicInt_exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero
-- name    : PadicInt.exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/cb30c107-4941-5af5-8aa6-aa2d9c1bff93
-- title:
--   Integral orthogonality: p^k v ∈ T^t+T^o
-- statement:
--   Let $p$ be a prime and let $T$ be a finitely generated module over the $p$-adic integers $\mathbb{Z}_p$ (an additive commutative group with a $\mathbb{Z}_p$-module structure of finite type). Let $\Gamma$ be a group, $\rho : \Gamma \to \operatorname{End}_{\mathbb{Z}_p}(T)$ a monoid homomorphism into the $\mathbb{Z}_p$-linear endomorphisms, $\chi : \Gamma \to \mathbb{Z}_p^{\times}$ a homomorphism of groups, $I$ a subgroup of $\Gamma$, and $e$ a $\mathbb{Z}_p$-bilinear form on $T$ which is assumed: alternating in the form $e(a,b) = -e(b,a)$ for all $a,b$; non-degenerate in the form that $e(a,b)=0$ for all $b$ forces $a=0$; and $\chi$-equivariant, $e(\rho(\gamma)a, \rho(\gamma)b) = \chi(\gamma)\, e(a,b)$ for all $\gamma \in \Gamma$ and $a,b \in T$. Let $T^{\mathrm t}, T^{\mathrm o} \subseteq T$ be $\mathbb{Z}_p$-submodules, each stable under $\rho(\gamma)$ for every $\gamma \in I$, with $e(x,y)=0$ for all $x \in T^{\mathrm t}$, $y \in T^{\mathrm o}$; assume there is some $k \in \mathbb{N}$ with $p^k (\rho(\tau)v - v) \in T^{\mathrm t} + T^{\mathrm o}$ for all $\tau \in I$ and all $v \in T$; assume the restriction of $e$ to $T^{\mathrm o}$ is non-degenerate, i.e. $y \in T^{\mathrm o}$ with $e(y,y')=0$ for all $y' \in T^{\mathrm o}$ is zero; and assume $\chi(\tau_0) \neq 1$ for some $\tau_0 \in I$. Then there is a single exponent $k \in \mathbb{N}$ such that every $v \in T$ with $e(v,x)=0$ for all $x \in T^{\mathrm t}$ satisfies $p^k v \in T^{\mathrm t} + T^{\mathrm o}$.
--
--   This is the $\mathbb{Z}_p$-lattice form, with denominators cleared by one uniform power of $p$, of the vector-space statement [`LinearMap.BilinForm.orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup`](thm.html#LinearMap.BilinForm.orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup) that the orthogonal complement of the toric part is contained in the sum of the toric and old parts. It is applied to the $p$-adic Tate module of a Jacobian with its Weil pairing, where the inertia subgroup $I$ acts through the cyclotomic character and the toric submodule is orthogonal to itself by Grothendieck's orthogonality, and is used in the level-lowering analysis of the $p$-divisible group at a prime of multiplicative reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PadicInt.exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero
    {p : ℕ} [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] {Γ : Type*} [Group Γ]
    (ρ : Γ →* Module.End ℤ_[p] T) (χ : Γ →* ℤ_[p]ˣ) (I : Subgroup Γ)
    (e : LinearMap.BilinForm ℤ_[p] T)
    (hskew : ∀ a b : T, e a b = - e b a)
    (hnondeg : ∀ a : T, (∀ b : T, e a b = 0) → a = 0)
    (hequiv : ∀ (γ : Γ) (a b : T), e (ρ γ a) (ρ γ b) = ((χ γ : ℤ_[p]ˣ) : ℤ_[p]) * e a b)
    (Tt To : Submodule ℤ_[p] T)
    (hTt : ∀ γ ∈ I, ∀ x ∈ Tt, ρ γ x ∈ Tt)
    (hTo : ∀ γ ∈ I, ∀ y ∈ To, ρ γ y ∈ To)
    (hISO : ∀ x ∈ Tt, ∀ y ∈ To, e x y = 0)
    (hCUT : ∃ k : ℕ, ∀ τ ∈ I, ∀ v : T, ((p : ℤ_[p]) ^ k) • (ρ τ v - v) ∈ Tt ⊔ To)
    (hOLD : ∀ y ∈ To, (∀ y' ∈ To, e y y' = 0) → y = 0)
    (hCYC : ∃ τ₀ ∈ I, χ τ₀ ≠ 1) :
    ∃ k : ℕ, ∀ v : T, (∀ x ∈ Tt, e v x = 0) → ((p : ℤ_[p]) ^ k) • v ∈ Tt ⊔ To := by sorry
