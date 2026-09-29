-- Prove2me | Theorems.Thm_Submodule_finrank_pi_univ_eq_sum
-- name    : Submodule.finrank_pi_univ_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/9b61de88-a23b-5f29-89fb-91227d97cd71
-- title:
--   Dimension of a product of subspaces
-- statement:
--   Let $k$ be a field, let $\iota$ be a finite index type, and let $(\Phi_v)_{v\in\iota}$ be a family of $k$-vector spaces (each $\Phi_v$ an additive commutative group with a $k$-module structure). Let $L$ assign to each $v$ a $k$-submodule $L_v \subseteq \Phi_v$, and assume each $L_v$ is finite-dimensional over $k$. Then the submodule $\mathtt{Submodule.pi Set.univ } L$ of the product $\prod_{v} \Phi_v$ — that is, the set of families $y$ with $y_v \in L_v$ for every $v$ in the index set $\mathrm{univ}$, hence for every $v\in\iota$ — has finite rank over $k$ equal to $\sum_{v\in\iota} \operatorname{finrank}_k L_v$. (Here $\operatorname{finrank}$ is the natural-number-valued rank, so the assertion is an equality in $\mathbb{N}$.)
--
--   This is the elementary fact that the dimension of a product of finitely many subspaces, viewed as a subspace of the product, is the sum of their dimensions. It supplies the term $\sum_v \dim_k \mathcal L_v$ recording the local conditions in the Greenberg–Wiles dimension formula for Selmer groups, and is used in the Galois-cohomology dimension bookkeeping via [`groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two`](thm.html#groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_finrank_pi_univ_eq_sum.lean

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Module

theorem Submodule.finrank_pi_univ_eq_sum
    {k : Type*} [Field k] {ι : Type*} [Fintype ι] {Φ : ι → Type*}
    [∀ v, AddCommGroup (Φ v)] [∀ v, Module k (Φ v)]
    (L : ∀ v, Submodule k (Φ v)) [∀ v, FiniteDimensional k (L v)] :
    finrank k (Submodule.pi Set.univ L) = ∑ v, finrank k (L v) := by sorry
