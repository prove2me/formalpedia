-- Prove2me | Theorems.Thm_PrepoLocal_Threshold_eq_4_auxiliary_solution
-- name    : PrepoLocal.Threshold.eq_4_auxiliary_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:52.601+00:00
-- url     : https://prove2.me/theorems/d97fcd05-1351-427c-bf6a-d70bb9dbc7ee
-- title:
--   Eq. (4), p. 9 — x̄∗ = min{(x₊)⁺, b} minimizes the auxiliary cost Ca on [0, b], x₊ = F̄⁻¹_{D−Q}(β∗)
-- statement:
--   In the single-cycle prepo model (standing assumptions as in the model definition), let $\beta^*=i\mu_T/(v-1)$ and let $x_+=\bar F^{-1}_{D-Q}(\beta^*)$ be a generalized $(1-\beta^*)$-fractile of the net demand $D-Q$: $\mathbb P(D-Q>x_+)\le\beta^*<\mathbb P(D-Q>y)$ for all $y<x_+$, or else $\beta^*\ge1$ and $x_+\le0$. Then
--   $$
--   \bar x^*=\min\{(x_+)^+,\,b\}
--   $$
--   minimizes the auxiliary cost $C_a(x)=\alpha\mu_D+i\mu_Tx+(1-\alpha)\mathbb E[(D-Q)^+]+(v-1)\mathbb E[(D-Q-x)^+]$ over the feasible prepo levels $0\le x\le b$.
--
--   This is the newsvendor solution of the auxiliary model, with demand replaced by net demand $D-Q$ and the critical shortage probability $\beta^*$ balancing the holding rate $i\mu_T$ against the shortage premium $v-1$.
--
--   **Formalization Note** "$\bar x^*=\arg\min_{x\le b}C_a(x)$" is read as "$\bar x^*$ is a minimizer of $C_a$ on $[0,b]$" (`IsMinOn`): $C_a$ need not be strictly convex. Prepo is a quantity, so the domain is $[0,b]$; every solution formula of the paper carries $(\cdot)^+$. No density of $D-Q$ is assumed, so $x_+$ is the least generalized fractile when it is finite; the case $\beta^*\ge1$, where the inverse is $-\infty$, is covered by the second alternative. When $\beta^*=0$ (no holding cost) and $D-Q$ is unbounded above, the paper's $x_+$ is $+\infty$ and no real $x_+$ satisfies the hypothesis, so the statement says nothing in that corner.
-- source:
--   Eftekhar, Song & Webster, Pre-Positioning and Local-Purchasing for Emergency Operations Under Budget and Supply Uncertainty, SSRN 3210309 (revision of Aug. 13, 2020), p. 9, §4.1, eq. (4)

import Mathlib
import Definitions.Def_PrepoLocal_Threshold_Model
open MeasureTheory ProbabilityTheory

namespace PrepoLocal.Threshold

/-- Eq. (4), p. 9: if `x₊ = F̄⁻¹_{D−Q}(β∗)`, then `x̄∗ = min{(x₊)⁺, b}` minimizes the
auxiliary cost `Ca` over the feasible prepo levels `[0, b]`. -/
theorem eq_4_auxiliary_solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ)
    (xplus : ℝ) (hx : IsNetFractile μ E (betaStar P μ E) xplus) :
    IsMinOn (Ca P μ E) (Set.Icc 0 P.b) (min (max xplus 0) P.b) := by sorry

end PrepoLocal.Threshold
