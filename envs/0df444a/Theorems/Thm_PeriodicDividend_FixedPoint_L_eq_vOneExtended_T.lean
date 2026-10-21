-- Prove2me | Theorems.Thm_PeriodicDividend_FixedPoint_L_eq_vOneExtended_T
-- name    : PeriodicDividend.FixedPoint.L_eq_vOneExtended_T
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T13:58:49.345472+00:00
-- url     : https://prove2.me/theorems/81574182-297f-46bd-be4c-06234a41b65c
-- title:
--   §3.3 — the one-period value at maturity $T$ equals $\mathcal L\varphi$: $v(T,x)=\mathcal L\varphi(x)$
-- statement:
--   In the periodic-dividend model of §3.1 (positive $\rho,\mu,\sigma,\lambda_f,\lambda_p,T$; the uncontrolled cash flow is a Brownian motion with drift $\mu$ and variance $\sigma^2$ with respect to a filtration satisfying the usual conditions), let $\varphi\in\mathcal C_A$ for some $A$. For an admissible issuance-only policy $I$ started from $x\ge0$, with ruin time $\theta$ and pre-maturity reserve $X_{t-}$, compare the one-period objective (3.2),
--
--   $$\mathbb E\Big[-\sum_{0\le s<T}e^{-\rho s}c(\Delta I_s)+e^{-\rho T}\varphi(X_{T-})\,\mathbf 1_{\{T<\theta\}}\Big],$$
--
--   with the arbitrary-maturity objective $J(t,x,I;\varphi)$ of §3.3 at $t=T$, which uses the survival indicator $\mathbf 1_{\{\theta\ge T\}}$. Then the two suprema over admissible policies coincide:
--
--   $$\mathcal L\varphi(x)=v(T,x)\qquad\text{for every }x\ge0 .$$
--
--   The paper records this as “It is clear that $v(T,x)=\mathcal L\varphi(x)$.” It is what lets the regularity of the one-period value $v$ (Theorem 3.6, including the boundary condition (3.5) at $t=T$) be transferred to $\mathcal L\varphi$ in the proof of Theorem 3.3.
--
--   **Formalization Note.** The two objectives differ only on the event $\{\theta=T\}$, where the reserve just before maturity is $0$. For a fixed $T$ this event is null under the Brownian dynamics, which is the implicit reason behind the paper's “it is clear”.
-- source:
--   Keppo, Reppen, Soner, Discrete dividend payments in continuous time, arXiv:1805.05077v2, §3.3 (One-period problem), sentence following the definitions of v and J and preceding Theorem 3.6: "It is clear that v(T,x) = Lφ(x)" (comparing (3.2) with the definition of v and J in §3.3)

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicDividend.FixedPoint

/-- §3.3: the one-period operator `L` of (3.2) is the arbitrary-maturity one-period value at maturity
`T`, `v(T, x) = Lφ(x)`. -/
theorem L_eq_vOneExtended_T {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params)
    (hS : p.Standing)
    (hU : UsualConditions P 𝔽)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma)
    (A : ℝ) (φ : ℝ≥0 → ℝ) (hφ : CA p A φ) (x : ℝ≥0) :
    Lop P 𝔽 C p φ x = vOneExtended P 𝔽 C p φ p.T x := by sorry

end PeriodicDividend.FixedPoint
