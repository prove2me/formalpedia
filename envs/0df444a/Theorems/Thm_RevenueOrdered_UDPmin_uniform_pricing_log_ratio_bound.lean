-- Prove2me | Theorems.Thm_RevenueOrdered_UDPmin_uniform_pricing_log_ratio_bound
-- name    : RevenueOrdered.UDPmin.uniform_pricing_log_ratio_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:43.658955+00:00
-- url     : https://prove2.me/theorems/8a8408c9-940e-4673-b316-b2aa1b9dee1e
-- title:
--   Corollary 4.7 — uniform pricing earns $\mathrm{OPT}_{\mathrm{UDP}}/(1+\ln(v_m/v_1))$ in $\mathrm{UDP}_{\min}$
-- statement:
--   Consider a $\mathrm{UDP}_{\min}$ instance with items $[n]$, $m\ge 1$ consumers, interest sets $B_i$ and valuations $0<v_1\le\dots\le v_m$. Let $\mathrm{OPT}_{\mathrm{UDP}}$ be the supremum of the seller's revenue over all positive price assignments and $\mathrm{UP}$ the supremum of the revenue over uniform prices $q>0$. Then
--   $$\mathrm{OPT}_{\mathrm{UDP}}\ \le\ \Big(1+\ln\frac{v_m}{v_1}\Big)\cdot\mathrm{UP},$$
--   that is, uniform pricing approximates the optimum revenue to within a factor of $1/(1+\ln\rho)$ with $\rho:=v_m/v_1$.
--
--   The bound depends only on the spread of the valuations, not on $n$ or $m$; the paper obtains it by combining Theorem 4.6 with Theorem 3.2.
--
--   **Formalization Note** Valuations are positive (the paper says non-negative; $\rho$ requires $v_1>0$). $v_m$ and $v_1$ are the maximum and minimum valuations, so no sorting is assumed. The statement holds for any number of items, including none (both sides are then $0$).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 20, Corollary 4.7

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Pricing

namespace RevenueOrdered.UDPmin

/-- Corollary 4.7 (Berbeglia–Joret, arXiv:1606.01371v3, p. 20): uniform pricing approximates the
optimum revenue of `UDP_min` to within a factor of `1/(1 + ln ρ)`, `ρ := v_m / v_1`, in product
form: `OPT_UDP ≤ (1 + ln(v_m / v_1)) · UP`. -/
theorem uniform_pricing_log_ratio_bound {X M : Type*} [Fintype X] [Fintype M] [Nonempty M]
    (I : Instance X M) :
    optUDP I ≤ (1 + Real.log (vMax I / vMin I)) * uniformRevenue I := by sorry

end RevenueOrdered.UDPmin
