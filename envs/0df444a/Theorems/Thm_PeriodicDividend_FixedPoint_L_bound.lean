-- Prove2me | Theorems.Thm_PeriodicDividend_FixedPoint_L_bound
-- name    : PeriodicDividend.FixedPoint.L_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:55.96298+00:00
-- url     : https://prove2.me/theorems/92c04779-7635-4d15-86f6-5e236885a918
-- title:
--   Proof of Theorem 3.3, p. 7 — bound on Lφ
-- statement:
--   Let $A\ge A^*=\mu T/(e^{\rho T}-1)$ and let $\phi\in\mathcal C_A$. For every initial reserve $x\ge0$, the one-period issuance value satisfies
--
--   $$0\le\mathcal L\phi(x)\le e^{-\rho T}x+A.$$
--
--   The bound supplies the finiteness of $\mathcal L\phi$ and its upper growth estimate, both needed to show that $\mathcal L$ maps $\mathcal C_A$ into $\widehat{\mathcal C}_A$.
--
--   **Formalization Note** The one-period value is an extended-real supremum. The upper bound places it in the finite reals.
-- source:
--   Keppo, Reppen, Soner, Discrete dividend payments in continuous time, arXiv:1805.05077v2, p. 7, proof of Theorem 3.3, Step 2

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicDividend.FixedPoint

/-- The bound in the proof of Theorem 3.3, Step 2. -/
theorem L_bound {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params)
    (hS : p.Standing)
    (hU : UsualConditions P 𝔽)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma)
    (A : ℝ) (hA : Astar p ≤ A) (φ : ℝ≥0 → ℝ) (hφ : CA p A φ)
    (x : ℝ≥0) :
    (0 : EReal) ≤ Lop P 𝔽 C p φ x ∧
      Lop P 𝔽 C p φ x ≤ ((Real.exp (-p.rho * p.T) * (x : ℝ) + A : ℝ) : EReal) := by sorry

end PeriodicDividend.FixedPoint
