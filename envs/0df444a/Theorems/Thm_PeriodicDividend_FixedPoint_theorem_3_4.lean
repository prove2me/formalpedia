-- Prove2me | Theorems.Thm_PeriodicDividend_FixedPoint_theorem_3_4
-- name    : PeriodicDividend.FixedPoint.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:15.334794+00:00
-- url     : https://prove2.me/theorems/68588cee-961c-451b-8497-511d87d6c965
-- title:
--   Theorem 3.4, p. 7 — the control-defined value is the unique fixed point
-- statement:
--   In the periodic-dividend model with positive discount, drift, volatility, period, fixed issuance cost and proportional issuance cost, let $V(x)$ be the supremum of expected discounted dividends less issuance costs over admissible controls. Put $A^*=\mu T/(e^{\rho T}-1)$. Then $V$ is finite at every $x\ge0$, belongs to $\mathcal C_{A^*}$, and is the unique fixed point of $\mathcal T=\mathcal D\circ\mathcal L$ in that class:
--
--   $$V\in\mathcal C_{A^*},\qquad\mathcal TV=V,\qquad
--   \phi\in\mathcal C_{A^*}\ \land\ \mathcal T\phi=\phi\Longrightarrow\phi=V.$$
--
--   The result identifies the fixed point with the original infinite-horizon control value, making the one-period operator a characterization of that value.
--
--   **Formalization Note** $V$ is defined from admissible controls, not from the fixed-point equation. The positive time interval and the impulse representation of equity issuance make explicit conventions used in §3.1.
-- source:
--   Keppo, Reppen, Soner, Discrete dividend payments in continuous time, arXiv:1805.05077v2, p. 7, Theorem 3.4 (Verification)

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicDividend.FixedPoint

/-- Theorem 3.4: the control-defined value is the unique fixed point in C_(A*). -/
theorem theorem_3_4 {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params)
    (hS : p.Standing)
    (hU : UsualConditions P 𝔽)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma) :
    ∃ Φ : ℝ≥0 → ℝ,
      (∀ x : ℝ≥0, valueFn P 𝔽 C p x = ((Φ x : ℝ) : EReal)) ∧
      CA p (Astar p) Φ ∧
      Top P 𝔽 C p Φ = Φ ∧
      ∀ ψ : ℝ≥0 → ℝ, CA p (Astar p) ψ →
        Top P 𝔽 C p ψ = ψ → ψ = Φ := by sorry

end PeriodicDividend.FixedPoint
