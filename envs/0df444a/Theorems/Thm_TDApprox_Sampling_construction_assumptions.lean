-- Prove2me | Theorems.Thm_TDApprox_Sampling_construction_assumptions
-- name    : TDApprox.Sampling.construction_assumptions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:45.936664+00:00
-- url     : https://prove2.me/theorems/062e522e-4548-4e2a-b4d6-bd32579398fb
-- title:
--   §9, pp. 24–25 — the construction satisfies Assumptions 1 and 2
-- statement:
--   Let $s_1\ne s_2$ and let $p$ be a probability distribution positive at every state with $5/(6\alpha)<p(s_2)<1$, where $5/6<\alpha<1$. Give every row of $P$ the distribution $p$, set every transition cost to zero, and use the one-dimensional basis $\phi(s_1)=1$, $\phi(s_2)=2$, and $\phi(i)=0$ elsewhere. Then Assumptions 1 and 2 hold, the cost-to-go is zero, and
--
--   $$\Pi T^{(0)}(\phi^{\mathsf T}r)=\phi^{\mathsf T}r\quad\Longleftrightarrow\quad r=0.$$
--
--   The construction identifies the unique projected fixed point around which the sampled iterates diverge.
--
--   **Formalization Note** The paper explicitly identifies $r^*=0$ and $J^*=0$; the unique-fixed-point clause makes the identity of $r^*$ precise. The paper's numbered states 1 and 2 are represented by arbitrary distinct states.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Theorem 3 proof, pp. 24–25; https://dspace.mit.edu/entities/publication/ab395d25-a6d3-407a-9589-60eaac58fd05

import Mathlib
import Definitions.Def_TDApprox_Sampling_Model

namespace TDApprox.Sampling

open MeasureTheory ProbabilityTheory

theorem construction_assumptions
    {S : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (s₁ s₂ : S) (hne : s₁ ≠ s₂) (α : ℝ) (hα₁ : (5 : ℝ) / 6 < α)
    (hα₂ : α < 1) (p : Measure S) [IsProbabilityMeasure p]
    (hp : ∀ i, 0 < p {i})
    (hp₂ : 5 / (6 * α) < (p {s₂}).toReal)
    (hp₂lt : (p {s₂}).toReal < 1) :
    let P := rowKernel p
    let φ := sampleFeature s₁ s₂
    Assumption1 P p (fun _ _ => 0) α ∧
      Assumption2 p φ ∧
      TDApprox.Conv.Jstar P (fun _ _ => 0) α = (fun _ => 0) ∧
      (∀ r : Fin 1 → ℝ,
        proj p φ (T0 P (fun _ _ => 0) α (fun i => dotProduct (φ i) r)) =
          (fun i => dotProduct (φ i) r) ↔ r = 0) := by sorry

end TDApprox.Sampling
