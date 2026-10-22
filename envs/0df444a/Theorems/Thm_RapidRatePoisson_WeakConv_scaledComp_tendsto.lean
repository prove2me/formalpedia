-- Prove2me | Theorems.Thm_RapidRatePoisson_WeakConv_scaledComp_tendsto
-- name    : RapidRatePoisson.WeakConv.scaledComp_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:18:11.983699+00:00
-- url     : https://prove2.me/theorems/a27a8f09-6061-49f9-9ac5-e82edabaec40
-- title:
--   Proof of Theorem 1, p. 4 — under Assumption 1, A_ε(t) = εA(t/ε) ⇒ λ*t as ε ↓ 0, for each t ≥ 0
-- statement:
--   Let $A=(A(t))_{t\ge0}$ be a real process on a probability space $(\Omega,\mathcal F,P)$ satisfying Assumption 1: for a deterministic $\lambda^*\in(0,\infty)$, $A(t)/t\to\lambda^*$ in probability as $t\to\infty$. Then for every $t\ge0$,
--   $$A_\varepsilon(t)=\varepsilon A(t/\varepsilon)\;\longrightarrow\;\lambda^* t\quad\text{in probability as }\varepsilon\downarrow0 .$$
--
--   This is the first sentence of the proof of Theorem 1: the scaled compensators converge, at each fixed time, to the compensator $\lambda^*t$ of a rate-$\lambda^*$ Poisson process, which is the hypothesis of the Poisson limit theorem the proof then applies.
--
--   **Formalization Note** "$\varepsilon\downarrow0$" is the filter of right neighbourhoods of $0$ in `ℝ≥0`, and "⇒" to a constant is Mathlib's convergence in measure. The page's identity $\varepsilon A(t/\varepsilon)=(\varepsilon/t)A(t/\varepsilon)\cdot t$ divides by $t$; at $t=0$ the claim is still stated (both sides tend to $0$). No compensator property is assumed: only Assumption 1 is used.
-- source:
--   Zheng, Honnappa & Glynn, arXiv:1807.06805v1, p. 4, proof of Theorem 1, first sentence

import Mathlib
import Definitions.Def_RapidRatePoisson_WeakConv_Model

namespace RapidRatePoisson.WeakConv
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem scaledComp_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ℝ≥0 → Ω → ℝ) (lamStar : ℝ≥0)
    (hA1 : Assumption1 P A lamStar) (t : ℝ≥0) :
    TendstoInMeasure P (fun (ε : ℝ≥0) ω => scaledComp A ε t ω) (𝓝[>] 0)
      (fun _ => (lamStar : ℝ) * t) := by sorry

end RapidRatePoisson.WeakConv
