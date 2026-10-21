-- Prove2me | Theorems.Thm_PeriodicDividend_FixedPoint_theorem_3_4_verification
-- name    : PeriodicDividend.FixedPoint.theorem_3_4_verification
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-20T13:46:25.138112+00:00
-- url     : https://prove2.me/theorems/78db25a9-93fd-415a-b440-f63383e5bc74
-- title:
--   Proof of Theorem 3.4, p. 7 — every fixed point of $\mathcal T$ in $\mathcal C_{A^*}$ is the value function
-- statement:
--   In the periodic-dividend model of §3.1 (positive discount rate $\rho$, drift $\mu$, volatility $\sigma$, period $T$, fixed issuance cost $\lambda_f$ and proportional issuance cost $\lambda_p$; the uncontrolled cash flow is a Brownian motion with drift $\mu$ and variance $\sigma^2$ with respect to a filtration satisfying the usual conditions), let $V(x)$ be the control-defined value function, i.e. the supremum over admissible periodic-dividend and equity-issuance policies of expected discounted dividends less discounted issuance costs, and let $A^*=\mu T/(e^{\rho T}-1)$.
--
--   If $\Phi\in\mathcal C_{A^*}$ is a fixed point of the one-period operator $\mathcal T=\mathcal D\circ\mathcal L$, i.e. $\mathcal T\Phi=\Phi$, then
--
--   $$V(x)=\Phi(x)\qquad\text{for every }x\ge 0$$
--
--   (in particular $V$ is finite).
--
--   This is the verification part of the proof of Theorem 3.4: unrolling $\Phi=\mathcal T^N\Phi$ gives an $N$-period dynamic-programming representation of $\Phi$ in terms of admissible issuance and dividend policies with terminal reward $e^{-\rho NT}\Phi(X_{NT})$; since $\Phi(x)\le x+A^*$ the terminal term vanishes as $N\to\infty$, identifying $\Phi$ with $V$. Together with the Banach fixed-point theorem applied to Theorem 3.3 it yields Theorem 3.4.
-- source:
--   Keppo, Reppen, Soner, Discrete dividend payments in continuous time, arXiv:1805.05077v2, p. 7, Theorem 3.4 (Verification) and its proof (identification of the fixed point of T with V)

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicDividend.FixedPoint

/-- Proof of Theorem 3.4 (verification step): every fixed point of `T` in `C_(A*)`
coincides with the control-defined value function. -/
theorem theorem_3_4_verification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params)
    (hS : p.Standing)
    (hU : UsualConditions P 𝔽)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma)
    (Φ : ℝ≥0 → ℝ) (hΦ : CA p (Astar p) Φ) (hfix : Top P 𝔽 C p Φ = Φ) :
    ∀ x : ℝ≥0, valueFn P 𝔽 C p x = ((Φ x : ℝ) : EReal) := by sorry

end PeriodicDividend.FixedPoint
