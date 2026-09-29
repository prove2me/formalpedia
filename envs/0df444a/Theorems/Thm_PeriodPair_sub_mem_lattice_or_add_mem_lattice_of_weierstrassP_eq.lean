-- Prove2me | Theorems.Thm_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq
-- name    : PeriodPair.sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/76700053-db5a-5638-b37f-e8c3dbceda16
-- title:
--   wp separates points up to sign modulo the lattice
-- statement:
--   Let $L$ be a period pair, with associated lattice `L.lattice` $\subset \mathbb{C}$ and Weierstrass function `L.weierstrassP`. Let $a, b \in \mathbb{C}$ be two complex numbers, neither of which lies in `L.lattice` (so that $\wp_L$ is defined and finite at both), and suppose $\wp_L(a) = \wp_L(b)$. The conclusion is the disjunction $a - b \in$ `L.lattice` or $a + b \in$ `L.lattice`; that is, $a \equiv b$ or $a \equiv -b$ modulo the lattice of $L$. No separate hypothesis is imposed on the period pair beyond what its definition carries, and the two cases of the conclusion are not asserted to be exclusive (both hold precisely when $2a$ and $2b$ lie in the lattice).
--
--   This is the classical statement that $\wp_L$ is an even elliptic function of order $2$, taking each finite value on exactly one pair $\pm z$ of classes in $\mathbb{C}/L.\mathrm{lattice}$. It is used in the study of sums of powers of $\wp$-values, namely by [`CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq`](thm.html#CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PeriodPair.sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq (L : PeriodPair) {a b : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (h : L.weierstrassP a = L.weierstrassP b) :
    a - b ∈ L.lattice ∨ a + b ∈ L.lattice := by sorry
