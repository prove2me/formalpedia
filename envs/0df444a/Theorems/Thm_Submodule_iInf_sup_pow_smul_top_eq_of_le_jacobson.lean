-- Prove2me | Theorems.Thm_Submodule_iInf_sup_pow_smul_top_eq_of_le_jacobson
-- name    : Submodule.iInf_sup_pow_smul_top_eq_of_le_jacobson
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/2bee86e1-1bf6-529a-9895-305d2f2274f1
-- title:
--   Submodules of finite modules are I-adically closed
-- statement:
--   Let $R$ be a commutative Noetherian ring and let $I \subseteq R$ be an ideal contained in the Jacobson radical of $R$, i.e. in `Ideal.jacobson ⊥`, the intersection of the maximal ideals of $R$. Let $M$ be an $R$-module whose underlying additive structure is an abelian group and which is finite as an $R$-module (finitely generated), and let $N$ be an $R$-submodule of $M$. The assertion is an equality of submodules of $M$: the infimum over all natural numbers $n$ of the submodules $N \sqcup I^n \cdot \top$ — that is, the sum $N + I^n M$, where $I^n \cdot \top$ denotes the pointwise scalar action of the ideal power $I^n$ on the full submodule $\top = M$ — equals $N$ itself. In other words, $\bigcap_{n \in \mathbb{N}} (N + I^n M) = N$, with the index $n$ ranging over all of $\mathbb{N}$ (including $n = 0$, whose term is $M$ and hence imposes no condition).
--
--   This is the submodule form of Krull's intersection theorem: every submodule of a finitely generated module is closed for the $I$-adic topology when $I$ lies in the Jacobson radical, no completeness being required. It is used in the project through [`Submodule.mem_of_forall_exists_sub_mem_pow_smul_top`](thm.html#Submodule.mem_of_forall_exists_sub_mem_pow_smul_top), which turns the approximation condition 'for every $n$ there is an element of $N$ congruent to $x$ modulo $I^n M$' into membership $x \in N$; the typical instance is $R$ a complete local Noetherian ring, for example $\mathbb{Z}_p$ with $I = (p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_iInf_sup_pow_smul_top_eq_of_le_jacobson.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem Submodule.iInf_sup_pow_smul_top_eq_of_le_jacobson
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M) :
    ⨅ n : ℕ, N ⊔ I ^ n • (⊤ : Submodule R M) = N := by sorry
