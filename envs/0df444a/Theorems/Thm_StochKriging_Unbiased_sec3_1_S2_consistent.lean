-- Prove2me | Theorems.Thm_StochKriging_Unbiased_sec3_1_S2_consistent
-- name    : StochKriging.Unbiased.sec3_1_S2_consistent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:46.363527+00:00
-- url     : https://prove2.me/theorems/2b284882-f91f-4792-a323-884c87ef3670
-- title:
--   §3.1, p. 365 — under Assumption 1, S²(x_i) is strongly consistent for V(x_i)
-- statement:
--   In the stochastic kriging model $\mathcal Y_j(\mathbf x)=\beta_0+\mathsf M(\mathbf x)+\varepsilon_j(\mathbf x)$ with distinct design points $\mathbf x_1,\dots,\mathbf x_k$ and noise variances $\mathsf V(\mathbf x_i)>0$, suppose Assumption 1 holds. Fix a design point $\mathbf x_i$ and let $\mathcal S^2_m(\mathbf x_i)$ be the sample variance (12) of the first $m$ replications $\mathcal Y_1(\mathbf x_i),\dots,\mathcal Y_m(\mathbf x_i)$. Then, almost surely,
--   $$\lim_{m\to\infty}\mathcal S^2_m(\mathbf x_i)=\mathsf V(\mathbf x_i).$$
--
--   This is the strong consistency of the stand-in $\mathcal S^2(\mathbf x_i)$ for the unobservable intrinsic variance, which justifies using it in place of $\mathsf V(\mathbf x_i)$.
--
--   **Formalization Note** The number of replications $m$ is the variable of the limit; the design's fixed $n_i$ does not appear. The values of (12) at $m=0,1$ (where it divides by $m-1\le0$) are Lean junk values and do not affect the limit.
-- source:
--   Ankenman, Nelson, Staum, Stochastic Kriging for Simulation Metamodeling, Proc. 2008 Winter Simulation Conference, p. 365, §3.1, sentence after display (12) (first conjunct)

import Mathlib
import Definitions.Def_StochKriging_Unbiased_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace StochKriging.Unbiased

/-- §3.1, p. 365 (first conjunct): under Assumption 1, `𝒮²(xᵢ)` is strongly consistent for
`V(xᵢ)`: the sample variance of the first `m` replications at `xᵢ` converges almost surely to
`V(xᵢ)` as `m → ∞`. -/
theorem sec3_1_S2_consistent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d k : ℕ} (x : Fin k → EuclideanSpace ℝ (Fin d))
    (hx : Function.Injective x) (β₀ : ℝ) (V : EuclideanSpace ℝ (Fin d) → ℝ≥0)
    (hV : ∀ i, 0 < V (x i)) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ) (hA : Assumption1 P M ε V x) (i : Fin k) :
    ∀ᵐ ω ∂P, Tendsto (fun m : ℕ => sampleVar (fun j => output β₀ M ε j (x i)) m ω) atTop
      (𝓝 (V (x i) : ℝ)) := by sorry

end StochKriging.Unbiased
