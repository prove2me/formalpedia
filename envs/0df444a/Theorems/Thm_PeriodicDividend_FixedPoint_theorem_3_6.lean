-- Prove2me | Theorems.Thm_PeriodicDividend_FixedPoint_theorem_3_6
-- name    : PeriodicDividend.FixedPoint.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:04.193155+00:00
-- url     : https://prove2.me/theorems/3949c805-b330-4bb3-98da-9fe057f91245
-- title:
--   Theorem 3.6, p. 8 — classical characterization of the one-period value
-- statement:
--   Fix $A\ge A^*$ and $\phi\in\mathcal C_A$. Let $v(t,x)$ be the value of the issuance-only problem with time to maturity $t\in[0,T]$ and starting reserve $x\ge0$. Then $v$ is finite, smooth on $Q=(0,T)\times(0,\infty)$, continuous on its closure, and belongs to $\mathcal C_A^T$. It is the unique function in that class satisfying
--
--   $$\rho v+\partial_t v-\mu\partial_x v-\tfrac12\sigma^2\partial_{xx}v=0\quad\text{on }Q,$$
--   $$v(t,0)=\max\{\mathcal I(v(t,\cdot))(0),0\},\qquad v(0,x)=\phi(x).$$
--
--   This identifies the value as the unique classical solution of the one-period problem and supplies the regularity used by Theorem 3.3.
--
--   **Formalization Note** The model uses the paper's non-strict survival indicator for arbitrary maturity and the pre-maturity reserve for the terminal reward.
-- source:
--   Keppo, Reppen, Soner, Discrete dividend payments in continuous time, arXiv:1805.05077v2, p. 8, Theorem 3.6, equations (3.4)–(3.6)

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model

open Set

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicDividend.FixedPoint

/-- Theorem 3.6: the issuance value is the unique classical solution of (3.4)–(3.6). -/
theorem theorem_3_6 {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params)
    (hS : p.Standing)
    (hU : UsualConditions P 𝔽)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma)
    (A : ℝ) (hA : Astar p ≤ A) (φ : ℝ≥0 → ℝ) (hφ : CA p A φ) :
    let u : ℝ → ℝ≥0 → ℝ := vOne P 𝔽 C p φ
    (∀ t ∈ Icc (0 : ℝ) p.T, ∀ x : ℝ≥0,
      vOneExtended P 𝔽 C p φ t x ≠ ⊤ ∧
      vOneExtended P 𝔽 C p φ t x ≠ ⊥) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => u q.1 (Real.toNNReal q.2)) (Q p) ∧
    ContinuousOn (fun q : ℝ × ℝ => u q.1 (Real.toNNReal q.2)) (Qbar p) ∧
    CTA p A u ∧
    SolvesPDE p (fun t x => u t (Real.toNNReal x)) ∧
    (∀ t ∈ Icc (0 : ℝ) p.T, u t 0 = max (Iop p (u t) 0) 0) ∧
    (∀ x : ℝ≥0, u 0 x = φ x) ∧
    ∀ w : ℝ → ℝ≥0 → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => w q.1 (Real.toNNReal q.2)) (Q p) →
      ContinuousOn (fun q : ℝ × ℝ => w q.1 (Real.toNNReal q.2)) (Qbar p) →
      CTA p A w →
      SolvesPDE p (fun t x => w t (Real.toNNReal x)) →
      (∀ t ∈ Icc (0 : ℝ) p.T, w t 0 = max (Iop p (w t) 0) 0) →
      (∀ x : ℝ≥0, w 0 x = φ x) →
      ∀ t ∈ Icc (0 : ℝ) p.T, ∀ x : ℝ≥0, w t x = u t x := by sorry

end PeriodicDividend.FixedPoint
