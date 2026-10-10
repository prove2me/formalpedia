-- Prove2me | Theorems.Thm_ReusablePricing_DPC_step2_bound
-- name    : ReusablePricing.DPC.step2_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:00.387452+00:00
-- url     : https://prove2.me/theorems/ca3f2dda-ead9-4058-a4dd-93363ee4378a
-- title:
--   EC.3 Step 2, ec8 — J^D − E[R^{DPC(ϵ)}] ≤ T·(ΨJϵ/n̲ + (4RJT/n)·exp{min{maxᵢCᵢ, n}·γ² − δγ})
-- statement:
--   Consider the basic reusable-resource model under its standing hypotheses, with A4 bound $R$ ($|r^t| \le R$ on $\Omega_\lambda$) and A5 constant $\Psi$. Let
--   $$1 < \epsilon \le \min\{\varphi_L,\varphi_U\}\cdot\underline n, \qquad \delta = \frac{(\underline n-1)(\epsilon-1)}{3\underline n}.$$
--   Then for every $\gamma \in (0,1]$ the revenue gap of DPC($\epsilon$) satisfies
--   $$J^D - \mathbf E\big[R^{DPC(\epsilon)}\big] \le T\cdot\Big(\frac{\Psi J\epsilon}{\underline n} + \frac{4RJT}{n}\exp\big\{\min\{\max_i C_i, n\}\cdot\gamma^2 - \delta\gamma\big\}\Big).$$
--
--   The first term is the cost of the buffer $\epsilon/\underline n$ on the high-probability event $\mathcal G(\epsilon,\delta)$; the second is the cost of its complement. Choosing $\gamma$ gives Theorem 1.
--
--   **Formalization Note.** The printed line has $\Psi J\epsilon/n$ and $r^u = \max_t\max_{\lambda\in\Omega_\lambda} r^t(\lambda)$. The statement uses $\underline n$, because the perturbation of DPC is $\epsilon/\underline n$, and the two-sided bound $R$ on $|r^t|$, because the loss on the complement of $\mathcal G$ needs a bound on $|r^t|$, not only on $r^t$. The printed factor $4$ and the outer factor $T$ are kept.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), pp. ec7–ec8, EC.3 Step 2, last display before "where the first inequality holds"

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control

namespace ReusablePricing.DPC

open Finset

/-- EC.3 Step 2 (ec8, last display of the chain): for `ε ∈ (1, min{φ_L, φ_U} n̲]`,
`δ = (n̲ - 1)(ε - 1)/(3 n̲)` and every `γ ∈ (0, 1]`,
`J^D - E[R^{DPC(ε)}] ≤ T (Ψ J ε / n̲ + (4 R J T / n) exp{min{max_i C_i, n} γ² - δ γ})`
(printed with `n` for `n̲` and `r^u` for `R`). -/
theorem step2_bound (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε δ : ℝ)
    (hP : P.Standing φL φU Ψ R nl)
    (hε1 : 1 < ε) (hε : ε ≤ min φL φU * nl)
    (hδ : δ = ((nl : ℝ) - 1) * (ε - 1) / (3 * nl))
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    P.JD - P.expRevenue ε nl ≤
      (P.T : ℝ) * (Ψ * P.J * ε / nl +
        4 * R * P.J * P.T / P.n * Real.exp (P.minCapN * γ ^ 2 - δ * γ)) := by sorry

end ReusablePricing.DPC
