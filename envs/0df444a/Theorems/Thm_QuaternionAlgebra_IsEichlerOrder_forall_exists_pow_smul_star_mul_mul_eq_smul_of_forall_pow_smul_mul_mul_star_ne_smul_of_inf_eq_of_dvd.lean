-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_forall_exists_pow_smul_star_mul_mul_eq_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
-- name    : QuaternionAlgebra.IsEichlerOrder.forall_exists_pow_smul_star_mul_mul_eq_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/acac1bbd-133e-5b9b-a97e-378f0702b0bb
-- title:
--   Flip: s⁻¹R₁s⊆Λ₁[1/r] when sR₁s⁻¹ fails
-- statement:
--   Fix primes $r,\bar r$ and a nonzero natural number $N$ with $r\nmid N$, $\bar r\nmid N$ and $N$ squarefree, and rationals $a_1,b_1$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a_1,b_1]$ is definite and ramified exactly at $\bar r$ in the sense of `IsDefiniteRamifiedExactlyAt`, i.e. $a_1<0$, $b_1<0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a_1,b_1]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $\bar r$ lies in $v$. Let $\Lambda_1,R_1$ be $\mathbb{Z}$-submodules with $\Lambda_1$ a maximal order (an order is a finitely generated $\mathbb{Z}$-submodule containing $1$, closed under multiplication and spanning the algebra over $\mathbb{Q}$; maximal means no order properly contains it), $R_1$ an Eichler order of level $N$ (an intersection of two maximal orders, the relative index of $R_1$ in the first of them being $N$) with $R_1\le\Lambda_1$, and let $\Lambda_{1}^{s}$ be a second maximal order with $R_1\le\Lambda_1^{s}$ and $\Lambda_1\cap\Lambda_1^{s}=R_1$. Let $\ell$ be a prime dividing $N$ and $s$ an element of the algebra with reduced norm $\mathrm{nrd}(s)=\ell$, where $\mathrm{nrd}(x)=x_{\mathrm{re}}^2-a_1x_{I}^2-b_1x_{J}^2+a_1b_1x_{K}^2$, such that $r^{c}s\in R_1$ and $r^{c'}\bar s\in R_1$ for some natural numbers $c,c'$ ($\bar s=\mathrm{star}\,s$). Assume finally that there is $z\in R_1$ with $r^{c}\,(s z \bar s)\neq \ell\, y$ for all natural numbers $c$ and all $y\in\Lambda_1$. Then for every $z\in R_1$ there are a natural number $K$ and $y\in\Lambda_1$ with $r^{K}\,(\bar s\, z\, s)=\ell\, y$.
--
--   This is the arithmetic of norm-$\ell$ elements of an Eichler order of squarefree level $N$ at a prime $\ell\mid N$, stated in the $r$-integral form used downstream: failure of $sR_1s^{-1}\subseteq\Lambda_1\otimes\mathbb{Z}[1/r]$ forces the opposite inclusion $s^{-1}R_1s\subseteq\Lambda_1\otimes\mathbb{Z}[1/r]$, the two possibilities corresponding to the double cosets of $\mathrm{diag}(\ell,1)$ and $\mathrm{diag}(1,\ell)$ for the local Iwahori order at $\ell$. It feeds the coset-graph analysis in the Čerednik–Drinfeld part of the argument, where conjugation by such Hecke elements is matched against edges of the graph.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_forall_exists_pow_smul_star_mul_mul_eq_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open QuaternionAlgebra
open scoped Quaternion

theorem QuaternionAlgebra.IsEichlerOrder.forall_exists_pow_smul_star_mul_mul_eq_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (s : ℍ[ℚ, a₁, b₁]) (hns : nrd s = (ℓ : ℚ))
    (hsR : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • s ∈ R₁) (hsR' : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • star s ∈ R₁)
    (hz : ∃ z : ℍ[ℚ, a₁, b₁], z ∈ R₁ ∧ ∀ (c : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ Λ₁ →
      ((r ^ c : ℕ) : ℚ) • (s * z * star s) ≠ (ℓ : ℚ) • y) :
    ∀ z : ℍ[ℚ, a₁, b₁], z ∈ R₁ → ∃ (K : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ Λ₁ ∧
      ((r ^ K : ℕ) : ℚ) • (star s * z * s) = (ℓ : ℚ) • y := by sorry
