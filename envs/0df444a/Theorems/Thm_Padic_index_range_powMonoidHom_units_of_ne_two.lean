-- Prove2me | Theorems.Thm_Padic_index_range_powMonoidHom_units_of_ne_two
-- name    : Padic.index_range_powMonoidHom_units_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/7cfaf989-7918-5726-ada3-35d3d6744260
-- title:
--   Index of p-th powers in ℚₚ^× is p² for odd p
-- statement:
--   Let $p$ be a prime number with $p \neq 2$. Consider the monoid homomorphism `powMonoidHom p` on the unit group $(\mathbb{Q}_p)^\times$ of the $p$-adic numbers, that is, the map $x \mapsto x^p$, which is a group homomorphism since $(\mathbb{Q}_p)^\times$ is commutative. Its range is the subgroup of $p$-th powers $((\mathbb{Q}_p)^\times)^p$. The assertion is that the index of this subgroup, in the sense of `Subgroup.index` (the cardinality of the coset space as a natural number, with value $0$ when that space is infinite), equals $p^2$; in particular the quotient $(\mathbb{Q}_p)^\times/((\mathbb{Q}_p)^\times)^p$ is finite of order $p^2$. The two ingredients cited are: every nonzero $x \in \mathbb{Q}_p$ can be written as $p^i (1+p)^j y^p$ with integers $0 \le i, j < p$ and $y \neq 0$; and, conversely, if $p^i (1+p)^j = y^p$ for integers $i, j$ and some $y \in \mathbb{Q}_p$, then $p \mid i$ and $p \mid j$. Thus the $p^2$ classes of the elements $p^i (1+p)^j$, $0 \le i, j < p$, exhaust the quotient and are pairwise distinct.
--
--   This is the local Kummer-theoretic computation $[\mathbb{Q}_p^\times : (\mathbb{Q}_p^\times)^p] = p^2$ for odd $p$, equivalently $\dim_{\mathbb{F}_p} \mathbb{Q}_p^\times/(\mathbb{Q}_p^\times)^p = 2$, the case $k = \mathbb{Q}_p$ of the standard formula for the index of $n$-th powers in a local field. It is used to obtain the cardinality of the quotient group $(\mathbb{Q}_p)^\times/((\mathbb{Q}_p)^\times)^p$ in [`Padic.natCard_units_quot_range_powMonoidHom_of_ne_two`](thm.html#Padic.natCard_units_quot_range_powMonoidHom_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Padic_index_range_powMonoidHom_units_of_ne_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Padic.index_range_powMonoidHom_units_of_ne_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ((powMonoidHom p : (ℚ_[p])ˣ →* (ℚ_[p])ˣ).range).index = p ^ 2 := by sorry
