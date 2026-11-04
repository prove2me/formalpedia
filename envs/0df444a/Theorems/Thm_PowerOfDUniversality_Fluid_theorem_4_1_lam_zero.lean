-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_theorem_4_1_lam_zero
-- name    : PowerOfDUniversality.Fluid.theorem_4_1_lam_zero
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T02:00:05.089586+00:00
-- url     : https://prove2.me/theorems/4c0faa44-d01b-4fa0-9a29-badcd9bfe57b
-- title:
--   Theorem 4.1, boundary case $\lambda = 0$ — fluid limit of JSQ with vanishing arrival rate
-- statement:
--   This is the boundary case $\lambda = 0$ of **Theorem 4.1** (fluid limit of the ordinary JSQ policy). It is needed to derive Theorem 2.1, which allows any limiting normalized arrival rate $\lambda\in[0,1)$, from Theorem 4.1 via Proposition 4.9, whereas Theorem 4.1 is stated for $\lambda>0$.
--
--   Consider systems $j=0,1,\dots$ with $N_j\ge 1$ parallel single-server queues, $N_j\to\infty$, common buffer $b\ge1$ (possibly infinite), Poisson arrivals of rate $\lambda_j\ge0$ and unit-mean exponential service, operating under the ordinary Join-the-Shortest-Queue policy. Assume
--   $$\frac{\lambda_j}{N_j}\to 0\qquad\text{and}\qquad \mathbf q^{N_j}(0)\xrightarrow{\ \mathbb P\ }\mathbf q^\infty\in\mathcal S\ \text{ in }\ell^1 .$$
--   Then any subsequence of the fluid-scaled occupancy processes $\{\mathbf q^{N_j}(t)\}_{t\ge0}$ has a further subsequence converging weakly (Skorohod $J_1$, $\ell^1$ topology) to a limit $\{\mathbf q(t)\}_{t\ge0}$ satisfying (4.5) with $\lambda=0$:
--   $$q_i(t)=q^\infty_i-\int_0^t\big(q_i(s)-q_{i+1}(s)\big)\,ds,\qquad i=1,\dots,b.$$
--
--   The formal statement is literally `theorem_4_1` with the hypothesis $\lambda>0$ replaced by $\lambda=0$ (weak convergence in coupling form, `SubseqFluidLimit`). The proof of Theorem 4.1 (martingale representation, Proposition 4.3, tightness via Lemmas 4.6–4.7) goes through verbatim; with $\lambda=0$ the arrival term vanishes on the fluid scale.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 17, Theorem 4.1 and (4.5), in the case λ = 0 used by Theorem 2.1 (p. 5) through Proposition 4.9 (p. 27)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Theorem 4.1, boundary case `λ = 0`** (p. 17, needed for Theorem 2.1 which allows
`λ(N)/N → λ ∈ [0, 1)`). Systems with `N_j → ∞` servers, buffer `b ≥ 1`, arrival rates
`λ_j ≥ 0` with `λ_j / N_j → 0`, run the ordinary JSQ policy from random initial occupancy
vectors with `q^{N_j}(0) → q^∞ ∈ 𝕊` in probability in `ℓ¹`. Then any subsequence of the
fluid-scaled processes has a further subsequence converging weakly (Skorohod `J₁`, `ℓ¹`) to a
limit satisfying (4.5) with `λ = 0`, i.e. `q_i(t) = q^∞_i − ∫_0^t (q_i(s) − q_{i+1}(s)) ds`. -/
theorem theorem_4_1_lam_zero (b : ℕ∞) (hb : 1 ≤ b)
    (Ns : ℕ → ℕ) (hNs1 : ∀ j, 1 ≤ Ns j) (hNs : Tendsto Ns atTop atTop)
    (lamN : ℕ → ℝ) (hlamN : ∀ j, 0 ≤ lamN j)
    (hlim : Tendsto (fun j => lamN j / (Ns j : ℝ)) atTop (𝓝 0))
    (qinf : ℕ → ℝ) (hqinf : qinf ∈ FluidSpace b)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sys : ∀ j, System P (Ns j) b (lamN j))
    (hinit : ∀ ε : ℝ, 0 < ε → Tendsto (fun j => P {ω | ENNReal.ofReal ε ≤
      l1dist (scaledOcc (Ns j) ((sys j).Q0 ω)) qinf}) atTop (𝓝 0)) :
    SubseqFluidLimit P b 0 qinf (fun j ω t => (sys j).fluid jsq ω t) := by sorry

end PowerOfDUniversality.Fluid
