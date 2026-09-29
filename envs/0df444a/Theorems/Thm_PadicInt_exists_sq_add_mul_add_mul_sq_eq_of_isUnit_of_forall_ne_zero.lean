-- Prove2me | Theorems.Thm_PadicInt_exists_sq_add_mul_add_mul_sq_eq_of_isUnit_of_forall_ne_zero
-- name    : PadicInt.exists_sq_add_mul_add_mul_sq_eq_of_isUnit_of_forall_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/71edeb40-bc2c-530c-ab00-c42040e95416
-- title:
--   Unramified quadratic norm form represents every p-adic unit
-- statement:
--   Let $p$ be a prime and let $t, n$ be integers such that the quadratic polynomial $X^2 - tX + n$ has no root in $\mathbb{Z}/p$: explicitly, for every $x \in \mathbb{Z}/p$ one has $x^2 - \bar t x + \bar n \neq 0$, where $\bar t, \bar n$ are the reductions of $t, n$. Let $u \in \mathbb{Z}_p$ be a unit of the ring of $p$-adic integers. Then there exist $c, d \in \mathbb{Z}_p$ with
--   $$c^2 + t\,c\,d + n\,d^2 = u,$$
--   the integers $t$ and $n$ being read in $\mathbb{Z}_p$ via the canonical ring map. Thus the binary integral quadratic form $c^2 + tcd + nd^2$ represents every unit of $\mathbb{Z}_p$ (not merely every unit up to squares, and with no assertion of uniqueness of $(c,d)$).
--
--   The form $c^2 + tcd + nd^2$ is the norm form of $\mathbb{Z}_p[\theta]$ with $\theta^2 = t\theta - n$ in the basis $1, \theta$; the irreducibility hypothesis modulo $p$ makes this the unramified quadratic extension of $\mathbb{Z}_p$, so the statement is the surjectivity of the norm map on units, written in coordinates. It is used in the construction of coordinates on maximal orders in quaternion algebras, in [`CerednikDrinfeld.QM.exists_isOrderCoord_of_isMaximalOrder`](thm.html#CerednikDrinfeld.QM.exists_isOrderCoord_of_isMaximalOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_sq_add_mul_add_mul_sq_eq_of_isUnit_of_forall_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicInt.exists_sq_add_mul_add_mul_sq_eq_of_isUnit_of_forall_ne_zero
    (p : ℕ) [Fact p.Prime] (t n : ℤ)
    (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0)
    (u : ℤ_[p]) (hu : IsUnit u) :
    ∃ c d : ℤ_[p], c ^ 2 + (t : ℤ_[p]) * c * d + (n : ℤ_[p]) * d ^ 2 = u := by sorry
