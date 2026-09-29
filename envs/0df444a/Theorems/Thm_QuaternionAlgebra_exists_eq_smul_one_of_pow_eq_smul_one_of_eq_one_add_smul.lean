-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul
-- name    : QuaternionAlgebra.exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/63a8983f-2c38-5cda-a682-9a4d7af27580
-- title:
--   Rigidity for γ ≡ 1 mod ℓ in a definite quaternion algebra
-- statement:
--   Let $a,b$ be rational numbers with $a<0$ and $b<0$, so that $\mathbb{H} = \mathbb{H}[\mathbb{Q},a,b]$ is a definite quaternion algebra over $\mathbb{Q}$. Let $L$ be a $\mathbb{Z}$-submodule of $\mathbb{H}$ which is an order in the sense of the predicate `IsOrder`, that is: $1 \in L$, $L$ is closed under multiplication, the $\mathbb{Q}$-span of $L$ is all of $\mathbb{H}$, and $L$ is finitely generated as a $\mathbb{Z}$-module. Let $\ell$ be a prime natural number with $\ell \ge 5$, and let $s$ be a natural number not divisible by $\ell$ (so in particular $s \neq 0$). Let $\gamma, y \in \mathbb{H}$ be such that $s\,y \in L$ and $\gamma = 1 + \ell\, y$, and suppose that for some integer $n \ge 1$ and some rational number $c$ one has $\gamma^{n} = c \cdot 1$. The conclusion is that $\gamma$ itself is a rational multiple of $1$: there exists $c' \in \mathbb{Q}$ with $\gamma = c' \cdot 1$. Here scalar multiplications are the $\mathbb{Q}$-action on $\mathbb{H}$ and the integer $\ell$, $s$ are viewed in $\mathbb{Q}$.
--
--   This is the quaternionic form of the Minkowski–Serre rigidity principle: an element of a definite quaternion algebra over $\mathbb{Q}$ which is congruent to $1$ modulo a prime $\ell \ge 5$ in the $s$-integral order $L$, and whose class in $\mathbb{H}^{\times}/\mathbb{Q}^{\times}$ has finite order, must already be central. It supplies the torsion-freeness input for [`CerednikDrinfeld.CosetGraph.exists_normal_finiteIndex_forall_isOfFinOrder_imp_eq_one`](thm.html#CerednikDrinfeld.CosetGraph.exists_normal_finiteIndex_forall_isOfFinOrder_imp_eq_one), which produces a normal subgroup of finite index all of whose elements of finite order are trivial; the argument runs through integrality of the reduced trace and reduced norm on an order, via [`QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq`](thm.html#QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul.lean

import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul
    {a b : ℚ} (ha : a < 0) (hb : b < 0) (L : Submodule ℤ ℍ[ℚ, a, b]) (hL : IsOrder L)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (s : ℕ) (hs : ¬ ℓ ∣ s)
    (γ y : ℍ[ℚ, a, b]) (hy : (s : ℚ) • y ∈ L) (hγ : γ = 1 + (ℓ : ℚ) • y)
    (n : ℕ) (hn : 0 < n) (c : ℚ) (hc : γ ^ n = c • (1 : ℍ[ℚ, a, b])) :
    ∃ c' : ℚ, γ = c' • (1 : ℍ[ℚ, a, b]) := by sorry
