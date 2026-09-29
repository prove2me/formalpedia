-- Prove2me | Theorems.Thm_StochasticOrders_PositiveDependence_pqd_order_convolution
-- name    : StochasticOrders.PositiveDependence.pqd_order_convolution
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:16:21.880153+00:00
-- url     : https://prove2.me/theorems/acc27b86-b2f3-448c-8940-134b04e52964
-- title:
--   Theorem 9.A.4 — closure of the PQD order under independent pairing and convolution
-- statement:
--   Let $X, Y, U, V$ be $n$-dimensional random vectors with laws $P_X, P_Y, P_U, P_V$, such that
--   $X \le_{PQD} Y$ and $U \le_{PQD} V$, with $X, U$ independent and $Y, V$ independent. Then
--
--   $$(\varphi_1(X_1,U_1),\dots,\varphi_n(X_n,U_n)) \le_{PQD} (\varphi_1(Y_1,V_1),\dots,\varphi_n(Y_n,V_n))$$
--
--   for all increasing functions $\varphi_1,\dots,\varphi_n : \mathbb{R}^2 \to \mathbb{R}$. This
--   is the general $n$-dimensional extension of Theorem 9.A.1 (the bivariate case, the closure
--   property Chapter IX opens with), and its own corollary $X+U \le_{PQD} Y+V$ is the PQD order's
--   convolution-closure result — the direct analogue, for positive dependence, of Chapter I's
--   Theorem 1.A.3(b) closure of the usual stochastic order.
--
--   **Formalization Note** Independence of $X,U$ (resp. $Y,V$) is formalized by taking their joint
--   law to be the **product measure** `Px.prod Pu` — a coupling with the given marginals in which
--   the two coordinates are independent by construction, exactly what "let $X$ and $U$ be
--   independent" supplies. Each $\varphi_i$ jointly increasing in both arguments is
--   `Monotone (Function.uncurry (φ i))` on `ℝ × ℝ` with its product order.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 392, Theorem 9.A.4

import Mathlib
import Definitions.Def_StochasticOrders_PositiveDependence_Orders

namespace StochasticOrders.PositiveDependence

open MeasureTheory

/-- Theorem 9.A.4 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 392): suppose the
four random vectors `X, Y, U, V` (each `n`-dimensional, with laws `Px, Py, Pu, Pv`) satisfy
`X ≤PQD Y` and `U ≤PQD V`, and suppose `X, U` are independent and `Y, V` are independent. Then
`(φ₁(X₁,U₁),…,φₙ(Xₙ,Uₙ)) ≤PQD (φ₁(Y₁,V₁),…,φₙ(Yₙ,Vₙ))` for all increasing functions `φᵢ`.
Independence is formalized by pairing the marginals through `Measure.prod`, the product law. -/
theorem pqd_order_convolution {n : ℕ} (Px Py Pu Pv : Measure (Fin n → ℝ))
    (hXY : PQDOrder Px Py) (hUV : PQDOrder Pu Pv)
    (φ : Fin n → ℝ → ℝ → ℝ) (hφ : ∀ i, Monotone (Function.uncurry (φ i)))
    (hφm : ∀ i, Measurable (Function.uncurry (φ i))) :
    PQDOrder
      (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => φ i (p.1 i) (p.2 i))
        (Px.prod Pu))
      (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => φ i (p.1 i) (p.2 i))
        (Py.prod Pv)) := by sorry

end StochasticOrders.PositiveDependence
