-- Prove2me | Theorems.Thm_StochasticOrders_PositiveDependence_pqd_order_convolution_v2
-- name    : StochasticOrders.PositiveDependence.pqd_order_convolution_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:32.00258+00:00
-- url     : https://prove2.me/theorems/0aa16eec-1a0d-4fa7-8f00-135a17b2d601
-- title:
--   Theorem 9.A.4 — closure of the PQD order under independent pairing and convolution (corrected: probability laws)
-- statement:
--   Let $X, Y, U, V$ be $n$-dimensional random vectors with laws $P_X, P_Y, P_U, P_V$ (probability measures on $\mathbb{R}^n$), such that $X \le_{PQD} Y$ and $U \le_{PQD} V$, with $X, U$ independent and $Y, V$ independent. Then
--
--   $$(\varphi_1(X_1,U_1),\dots,\varphi_n(X_n,U_n)) \le_{PQD} (\varphi_1(Y_1,V_1),\dots,\varphi_n(Y_n,V_n))$$
--
--   for all increasing Borel functions $\varphi_1,\dots,\varphi_n : \mathbb{R}^2 \to \mathbb{R}$. This is the general $n$-dimensional extension of Theorem 9.A.1, and its corollary $X+U \le_{PQD} Y+V$ is the PQD order's convolution-closure result.
--
--   **Formalization Note.** The retired version let the four laws be arbitrary measures on $\mathbb{R}^n$; the PQD order compares orthant masses through `ENNReal.toReal`, under which an orthant of infinite mass reads as $0$, so $X \le_{PQD} Y$ could hold vacuously (refuted with $P_Y = 0$ and an infinite $P_X$). The new statement makes explicit that the laws of random vectors are probability measures (`[IsProbabilityMeasure Px]`, …), for which `survivalVec`/`cdfVec` are the honest joint survival and distribution functions in $[0,1]$. Independence of $X,U$ (resp. $Y,V$) is formalized by taking the joint law to be the product measure `Px.prod Pu`; each $\varphi_i$, jointly increasing in both arguments, is `Monotone (Function.uncurry (φ i))` for the product order on $\mathbb{R}^2$, and is Borel, as the book's $\varphi_i(X_i,U_i)$ being random variables requires (and as `Measure.map` needs to be the image law). No correction to the printed source.
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
Independence is formalized by pairing the marginals through `Measure.prod`, the product law.

Corrected version (`_v2`) of `pqd_order_convolution`: the laws of random vectors are probability
measures, now explicit as `[IsProbabilityMeasure Px]` etc. The retired statement admitted
arbitrary measures, for which an orthant of infinite mass reads as `0` through `ENNReal.toReal` in
`survivalVec`/`cdfVec`, so `X ≤PQD Y` could hold vacuously. The `φᵢ` are Borel (the book's
`φᵢ(Xᵢ,Uᵢ)` must be random variables, and `Measure.map` of a non-measurable map is `0`). -/
theorem pqd_order_convolution_v2 {n : ℕ} (Px Py Pu Pv : Measure (Fin n → ℝ))
    [IsProbabilityMeasure Px] [IsProbabilityMeasure Py] [IsProbabilityMeasure Pu]
    [IsProbabilityMeasure Pv]
    (hXY : PQDOrder Px Py) (hUV : PQDOrder Pu Pv)
    (φ : Fin n → ℝ → ℝ → ℝ) (hφ : ∀ i, Monotone (Function.uncurry (φ i)))
    (hφm : ∀ i, Measurable (Function.uncurry (φ i))) :
    PQDOrder
      (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => φ i (p.1 i) (p.2 i))
        (Px.prod Pu))
      (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => φ i (p.1 i) (p.2 i))
        (Py.prod Pv)) := by sorry

end StochasticOrders.PositiveDependence
