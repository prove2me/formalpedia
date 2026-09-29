-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf
-- name    : QuaternionAlgebra.IsOrder.pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/991b3132-9824-5a77-9d3a-1ca025deb280
-- title:
--   Units of definite rational quaternion orders satisfy u¹²=1
-- statement:
--   Let $a,b$ be negative rationals and let $\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra over $\mathbb{Q}$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project's predicate [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11), that is: $1 \in \Lambda$; $\Lambda$ is closed under multiplication; the $\mathbb{Q}$-span of $\Lambda$ is all of $\mathbb{H}[\mathbb{Q},a,b]$; and $\Lambda$ is finitely generated as a $\mathbb{Z}$-module. Call an element $u$ of the algebra a unit of $\Lambda$ (the predicate [`QuaternionAlgebra.IsUnitOf`](def/QuaternionAlgebra_Order.html#L21)) when $u \in \Lambda$ and there is $v \in \Lambda$ with $uv = 1$ and $vu = 1$. The conclusion is a conjunction: first, every unit $u$ of $\Lambda$ satisfies $u^{12} = 1$; second, for every prime $p$ with $p \ge 5$, $p$ does not divide $\mathrm{Nat.card}$ of the subtype of elements of $\mathbb{H}[\mathbb{Q},a,b]$ that are units of $\Lambda$ (for a finite type this natural-number cardinality is the order of the unit group).
--
--   This is the standard finiteness-and-torsion statement for the unit group of an order in a definite rational quaternion algebra: such unit groups are among $C_2, C_4, C_6, Q_8, Q_{12}$ and $\mathrm{SL}_2(\mathbb{F}_3)$, all of exponent dividing $12$ and of order divisible only by $2$ and $3$. It builds on [`QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one`](thm.html#QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one) (finiteness of the unit group and reduced norm $1$), and is used in the Čerednik–Drinfeld coset-graph arguments, where control of the orders of finite stabilisers is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf
    {a b : ℚ} (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) :
    (∀ u : ℍ[ℚ, a, b], QuaternionAlgebra.IsUnitOf Λ u → u ^ 12 = 1) ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card {u : ℍ[ℚ, a, b] // QuaternionAlgebra.IsUnitOf Λ u} := by sorry
