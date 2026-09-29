-- Prove2me | Theorems.Thm_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue
-- name    : PowerSeries.exists_finset_sum_order_taylorShift_eq_order_map_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/5ad4a7ce-19d0-59dc-a1d8-dbf6107992c0
-- title:
--   Weierstrass zero count in the open unit disc
-- statement:
--   Let $O$ be a local domain which is adically complete for its maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal O`, and let $L$ be a nontrivially normed field which is complete, algebraically closed, and whose distance is ultrametric. Let $\iota\colon O \to L$ be a ring homomorphism which is injective, satisfies $\|\iota(x)\| \le 1$ for every $x \in O$, and satisfies $\|\iota(x)\| < 1$ for every $x \in \mathfrak m$. Let $F \in O[[q]]$ be a power series whose reduction $F \bmod \mathfrak m$, the image of $F$ under the residue map $O \to O/\mathfrak m$ applied coefficientwise, is non-zero. For $r \in L$ put $T_r(\iota F) := \mathrm{mk}\bigl(n \mapsto \sum_{k}^{\prime} \iota(a_{n+k})\binom{n+k}{n} r^{k}\bigr)$, the power series over $L$ whose $n$-th coefficient is the (unconditional) sum of the indicated series in $L$, where $a_{j}$ is the $j$-th coefficient of $F$; this is the Taylor shift $q \mapsto r + q$ of $\iota F$. The assertion is that there is a finite set $S \subseteq L$ whose elements are exactly those $r$ with $\|r\| < 1$ and $\operatorname{ord} T_r(\iota F) > 0$, and that $\sum_{r \in S} \operatorname{ord} T_r(\iota F) = \operatorname{ord}(F \bmod \mathfrak m)$, an identity of elements of $\mathbb{N} \cup \{\infty\}$.
--
--   This is the counting half of $p$-adic Weierstrass preparation: the Weierstrass degree of $F$, namely the order of its reduction modulo $\mathfrak m$, equals the number of zeros of $\iota F$ in the open unit disc of $L$ counted with multiplicity, the multiplicity at $r$ being recorded as the order in $q$ of the Taylor shift of $\iota F$ at $r$. It is used in the passage between $q$-expansions and divisors on the analytic disc, through [`ModularCurve.PlaceSpecialization.exists_sum_ord_isInftySide_eq_order_sub_order`](thm.html#ModularCurve.PlaceSpecialization.exists_sum_ord_isInftySide_eq_order_sub_order).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PowerSeries.exists_finset_sum_order_taylorShift_eq_order_map_residue
    {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [IsAlgClosed L]
    (ι : O →+* L) (hι : Function.Injective ι) (hι1 : ∀ x, ‖ι x‖ ≤ 1)
    (hιm : ∀ x ∈ IsLocalRing.maximalIdeal O, ‖ι x‖ < 1)
    (F : PowerSeries O) (hF : F.map (IsLocalRing.residue O) ≠ 0) :
    ∃ S : Finset L, (∀ r, r ∈ S ↔ ‖r‖ < 1 ∧
        0 < (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (F.map ι) * ((n + k).choose n : L) * r ^ k).order) ∧
      ∑ r ∈ S, (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (F.map ι) * ((n + k).choose n : L) * r ^ k).order
        = (F.map (IsLocalRing.residue O)).order := by sorry
