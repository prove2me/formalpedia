-- Prove2me | Theorems.Thm_RapidRatePoisson_WeakConv_scaledComp_tendsto_of_A0
-- name    : RapidRatePoisson.WeakConv.scaledComp_tendsto_of_A0
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T11:13:17.175671+00:00
-- url     : https://prove2.me/theorems/61fa492f-5e1e-4675-b1b9-3867dc152481
-- title:
--   Proof of Theorem 1, p. 4 — Assumption 1 and A(0)=0 give A_ε(t) = εA(t/ε) ⇒ λ*t as ε ↓ 0, for each t ≥ 0
-- statement:
--   Let $A=(A(t))_{t\ge0}$ be a real process on a probability space $(\Omega,\mathcal F,P)$ with $A(0)=0$ (as for any compensator), satisfying Assumption 1: for a deterministic $\lambda^*\in(0,\infty)$, $A(t)/t\to\lambda^*$ in probability as $t\to\infty$. Then for every $t\ge0$,
--   $$A_\varepsilon(t)=\varepsilon A(t/\varepsilon)\;\longrightarrow\;\lambda^* t\quad\text{in probability as }\varepsilon\downarrow0 .$$
--
--   This is the first sentence of the proof of Theorem 1, using the identity $\varepsilon A(t/\varepsilon)=t\cdot A(t/\varepsilon)/(t/\varepsilon)$ for $t>0$ and $t/\varepsilon\to\infty$.
--
--   **Formalization Note** This is the milestone `scaledComp_tendsto` with the hypothesis $A(0)=0$ added, which holds for the compensator in the paper. Without it the milestone's $t=0$ case fails: $\varepsilon A(0)\to 0$ in (outer) measure can fail for a non-measurable $A(0)$ (the milestone has been disproved). "$\varepsilon\downarrow0$" is the filter of right neighbourhoods of $0$ in `ℝ≥0`, and convergence to a constant is Mathlib's convergence in measure.
-- source:
--   Zheng, Honnappa & Glynn, arXiv:1807.06805v1, p. 4, proof of Theorem 1 (first sentence), with Assumption 1, p. 4

import Mathlib
import Definitions.Def_RapidRatePoisson_WeakConv_Model

namespace RapidRatePoisson.WeakConv
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem scaledComp_tendsto_of_A0 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ℝ≥0 → Ω → ℝ) (lamStar : ℝ≥0)
    (hA0 : ∀ ω, A 0 ω = 0) (hA1 : Assumption1 P A lamStar) (t : ℝ≥0) :
    TendstoInMeasure P (fun (ε : ℝ≥0) ω => scaledComp A ε t ω) (𝓝[>] 0)
      (fun _ => (lamStar : ℝ) * t) := by sorry

end RapidRatePoisson.WeakConv
