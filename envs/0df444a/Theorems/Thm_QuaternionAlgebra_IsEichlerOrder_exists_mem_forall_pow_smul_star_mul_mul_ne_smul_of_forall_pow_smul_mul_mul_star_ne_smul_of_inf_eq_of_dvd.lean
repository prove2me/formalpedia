-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_forall_pow_smul_star_mul_mul_ne_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
-- name    : QuaternionAlgebra.IsEichlerOrder.exists_mem_forall_pow_smul_star_mul_mul_ne_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/855f76ac-d79c-5435-b76f-d3271ec7983e
-- title:
--   Norm-ℓ conjugation flip between twin maximal orders
-- statement:
--   Let $r$, $\bar r$ be primes and $N \geq 1$ with $r \nmid N$, $\bar r \nmid N$ and $N$ squarefree. Let $a_1, b_1 \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q}, a_1, b_1]$ satisfies `IsDefiniteRamifiedExactlyAt` $\bar r$, i.e. $a_1 < 0$, $b_1 < 0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q}, a_1, b_1] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $\bar r \in v$. Let $\Lambda_1$, $\Lambda_1^s$ be $\mathbb{Z}$-submodules that are maximal orders (orders in the sense of `IsOrder`: containing $1$, closed under multiplication, spanning the algebra over $\mathbb{Q}$, finitely generated, and maximal among such), and let $R_1$ be an Eichler order of level $N$, i.e. an intersection of two maximal orders of relative index $N$ in the first; assume $R_1 \leq \Lambda_1$, $R_1 \leq \Lambda_1^s$ and $\Lambda_1 \sqcap \Lambda_1^s = R_1$. Let $\ell$ be a prime dividing $N$ and $s$ an element of reduced norm $\mathrm{nrd}(s) = \ell$ such that $r^c s \in R_1$ and $r^{c'} \bar s \in R_1$ for some $c, c'$. Assume there is $z \in R_1$ with $r^c \cdot (s z \bar s) \neq \ell \cdot y$ for all $c \in \mathbb{N}$ and all $y \in \Lambda_1$. Then there is $x \in R_1$ with $r^c \cdot (\bar s x s) \neq \ell \cdot y$ for all $c \in \mathbb{N}$ and all $y \in \Lambda_1^s$.
--
--   Stated multiplicatively, this says that if conjugation by $s$ fails to carry $R_1$ into $\Lambda_1 \otimes \mathbb{Z}[1/r]$, then conjugation by $\bar s$ (i.e. by $s^{-1}$ up to the norm) fails to carry $R_1$ into the twin maximal order $\Lambda_1^s \otimes \mathbb{Z}[1/r]$; the mechanism is the local structure at $\ell$, where $R_1$ is an Iwahori order and the norm-$\ell$ elements fall into three double cosets. It is used in the analysis of level-$\ell$ Hecke correspondences on the fake elliptic curves attached to the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_forall_pow_smul_star_mul_mul_ne_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open QuaternionAlgebra
open scoped Quaternion

theorem QuaternionAlgebra.IsEichlerOrder.exists_mem_forall_pow_smul_star_mul_mul_ne_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (s : ℍ[ℚ, a₁, b₁]) (hns : nrd s = (ℓ : ℚ))
    (hsR : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • s ∈ R₁) (hsR' : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • star s ∈ R₁)
    (hz : ∃ z : ℍ[ℚ, a₁, b₁], z ∈ R₁ ∧ ∀ (c : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ Λ₁ →
      ((r ^ c : ℕ) : ℚ) • (s * z * star s) ≠ (ℓ : ℚ) • y) :
    ∃ x : ℍ[ℚ, a₁, b₁], x ∈ R₁ ∧ ∀ (c : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ Λ₁s →
      ((r ^ c : ℕ) : ℚ) • (star s * x * s) ≠ (ℓ : ℚ) • y := by sorry
