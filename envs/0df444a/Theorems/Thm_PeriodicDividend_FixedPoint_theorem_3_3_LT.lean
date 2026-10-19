-- Prove2me | Theorems.Thm_PeriodicDividend_FixedPoint_theorem_3_3_LT
-- name    : PeriodicDividend.FixedPoint.theorem_3_3_LT
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:08.045613+00:00
-- url     : https://prove2.me/theorems/a90cf84f-89f5-452a-9ba6-acc141228fa6
-- title:
--   Theorem 3.3, pp. 6–7 — L maps C_A into Ĉ_A and T contracts
-- statement:
--   Let $A\ge A^*=\mu T/(e^{\rho T}-1)$. The one-period financing operator maps $\mathcal C_A$ to $\widehat{\mathcal C}_A$, so $\mathcal T=\mathcal D\circ\mathcal L$ maps $\mathcal C_A$ to itself. For any $\phi,\psi\in\mathcal C_A$ whose pointwise distance is at most $K$,
--
--   $$|\mathcal T\phi(x)-\mathcal T\psi(x)|\le e^{-\rho T}K\qquad(x\ge0).$$
--
--   Thus $\mathcal T$ is a strict contraction in the uniform metric. This is the fixed-point input to Theorem 3.4.
--
--   **Formalization Note** The explicit factor $e^{-\rho T}$ and $A^*$ are taken from the proof on p. 7.
-- source:
--   Keppo, Reppen, Soner, Discrete dividend payments in continuous time, arXiv:1805.05077v2, pp. 6–7, Theorem 3.3, second sentence and proof Steps 2–3

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicDividend.FixedPoint

/-- Second assertion of Theorem 3.3, with the contraction factor from its proof. -/
theorem theorem_3_3_LT {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params)
    (hS : p.Standing)
    (hU : UsualConditions P 𝔽)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma)
    (A : ℝ) (hA : Astar p ≤ A) :
    (∀ φ : ℝ≥0 → ℝ, CA p A φ →
      ChatA p A (fun x => (Lop P 𝔽 C p φ x).toReal) ∧
      CA p A (Top P 𝔽 C p φ)) ∧
    (∀ (φ ψ : ℝ≥0 → ℝ) (K : ℝ),
      CA p A φ → CA p A ψ →
      (∀ x, |φ x - ψ x| ≤ K) →
      ∀ x, |Top P 𝔽 C p φ x - Top P 𝔽 C p ψ x| ≤
        Real.exp (-p.rho * p.T) * K) := by sorry

end PeriodicDividend.FixedPoint
