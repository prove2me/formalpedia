-- Prove2me | Theorems.Thm_RingHom_exists_mem_forall_mem_range_of_isOpen
-- name    : RingHom.exists_mem_forall_mem_range_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/ba8a012a-cd6c-533c-adbb-ff277e2a7322
-- title:
--   Open subsets of ℂⁿ contain points with coordinates in σ(F)
-- statement:
--   Let $n$ be a natural number and let $F$ be an algebraically closed field of characteristic zero, and let $\sigma \colon F \to \mathbb{C}$ be a ring homomorphism. Let $U$ be a subset of $\mathrm{Fin}\,n \to \mathbb{C}$, that is of $\mathbb{C}^n$ with its product topology, and assume $U$ is open and non-empty. The assertion is that there exists a point $b \in U$ such that for every index $j$ the coordinate $b_j$ lies in the range of $\sigma$, i.e. $b_j = \sigma(a_j)$ for some $a_j \in F$. Thus every non-empty open subset of $\mathbb{C}^n$ contains a point all of whose coordinates are values of $\sigma$; equivalently, $\sigma(F)^n$ is dense in $\mathbb{C}^n$. No algebraicity or countability hypothesis on $F$ beyond being algebraically closed of characteristic zero is required, and $n = 0$ is permitted (then the unique point of the one-point space works).
--
--   This is the descent device by which an existence statement proved analytically over $\mathbb{C}$ for a parameter ranging over a non-empty open set can be realised by a parameter with coordinates in the image of a prescribed embedding $\sigma$ of an abstract algebraically closed field of characteristic zero. It is used in the choice of hyperplane sections on modular curves, in [`ModularCurve.JZero.exists_hyperplaneSection_defect_le`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_defect_le) and [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_exists_mem_forall_mem_range_of_isOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem RingHom.exists_mem_forall_mem_range_of_isOpen {n : ℕ} {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ b ∈ U, ∀ j, b j ∈ Set.range σ := by sorry
