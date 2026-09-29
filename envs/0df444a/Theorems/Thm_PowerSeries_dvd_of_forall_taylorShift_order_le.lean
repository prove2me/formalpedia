-- Prove2me | Theorems.Thm_PowerSeries_dvd_of_forall_taylorShift_order_le
-- name    : PowerSeries.dvd_of_forall_taylorShift_order_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/70f0108d-3baf-59a5-b709-0ba6012090f8
-- title:
--   A p-adic Weierstrass divisibility criterion via Taylor shifts
-- statement:
--   Let $\mathcal O$ be a commutative local ring which is adically complete for its maximal ideal $\mathfrak m$, and let $L$ be a nontrivially normed field which is complete, whose distance is ultrametric, and which is algebraically closed. Let $\iota\colon\mathcal O\to L$ be a ring homomorphism which is injective, satisfies $\|\iota(x)\|\le 1$ for every $x\in\mathcal O$, and satisfies $\|\iota(x)\|<1$ for every $x\in\mathfrak m$. Let $P,Q\in\mathcal O[[q]]$ be formal power series and assume that the image of $Q$ under the residue map $\mathcal O\to\mathcal O/\mathfrak m$, applied coefficientwise, is nonzero, i.e. some coefficient of $Q$ is a unit. For $F\in\mathcal O[[q]]$ and $r\in L$ let $T_rF$ denote the power series over $L$ whose $n$-th coefficient is the (unconditional) sum $\sum_{k\ge 0}\iota(a_{n+k})\binom{n+k}{n}r^k$, where $a_m$ is the $m$-th coefficient of $F$; formally this is the Taylor shift $F(r+q)$ of the image of $F$ in $L[[q]]$. Assume that for every $r\in L$ with $\|r\|<1$ one has $\operatorname{ord}_q T_rQ\le\operatorname{ord}_q T_rP$, the orders being taken in $\mathbb N\cup\{\infty\}$. Then $Q$ divides $P$ in $\mathcal O[[q]]$.
--
--   This is a divisibility criterion of Weierstrass preparation and division type: a power series over $\mathcal O$ whose reduction mod $\mathfrak m$ is nonzero divides $P$ as soon as its vanishing orders at all points of the open unit disc, measured through $\iota$, are dominated by those of $P$. It is used in the passage between $q$-expansions at a cusp and functions on the disc, in [`ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg`](thm.html#ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg) and [`ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg_xH`](thm.html#ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg_xH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_dvd_of_forall_taylorShift_order_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PowerSeries.dvd_of_forall_taylorShift_order_le
    {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [IsAlgClosed L]
    (ι : O →+* L) (hι : Function.Injective ι) (hι1 : ∀ x, ‖ι x‖ ≤ 1)
    (hιm : ∀ x ∈ IsLocalRing.maximalIdeal O, ‖ι x‖ < 1)
    (P Q : PowerSeries O) (hQ : Q.map (IsLocalRing.residue O) ≠ 0)
    (h : ∀ r : L, ‖r‖ < 1 →
      (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (Q.map ι) * ((n + k).choose n : L) * r ^ k).order
        ≤ (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (P.map ι) * ((n + k).choose n : L) * r ^ k).order) :
    Q ∣ P := by sorry
