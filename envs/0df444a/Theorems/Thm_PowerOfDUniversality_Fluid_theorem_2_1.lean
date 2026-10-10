-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_theorem_2_1
-- name    : PowerOfDUniversality.Fluid.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:27.077114+00:00
-- url     : https://prove2.me/theorems/c795c2aa-8102-4512-8a4e-b99be416a824
-- title:
--   Theorem 2.1 — universality of the fluid limit for JSQ(d(N)) with d(N) → ∞
-- statement:
--   Consider systems with $N=1,2,\dots$ parallel single-server queues, a common buffer $b\ge1$ (possibly infinite), Poisson arrivals of rate $\lambda(N)\ge0$ and unit-mean exponential service, under the JSQ($d(N)$) scheme: each arriving task joins a shortest queue among $d(N)$ servers sampled uniformly at random, $1\le d(N)\le N$. Assume that
--   $$\mathbf q^{d(N)}(0)\to\mathbf q^\infty\ \text{in }\mathcal S\qquad\text{and}\qquad \frac{\lambda(N)}{N}\to\lambda<1\qquad\text{as } N\to\infty,$$
--   and that $d(N)\to\infty$. Then any subsequence of the sequence of fluid-scaled occupancy processes $\{\mathbf q^{d(N)}(t)\}_{t\ge0}$ has a further subsequence that converges weakly with respect to the Skorohod $J_1$ topology to a limit $\{\mathbf q(t)\}_{t\ge0}$ satisfying
--   $$q_i(t)=q^\infty_i+\lambda\int_0^t p_{i-1}(\mathbf q(s))\,ds-\int_0^t\big(q_i(s)-q_{i+1}(s)\big)\,ds,\qquad i=1,\dots,b. \tag{2.1}$$
--
--   The fluid dynamics do not depend on the growth rate of $d(N)$, as long as $d(N)\to\infty$: the scheme behaves on the fluid scale exactly like the ordinary JSQ policy, while it needs only $d(N)$ queue-length inquiries per task instead of $N$.
--
--   **Formalization Note** Here $\mathbf q^{d(N)}(t)=\mathbf Q^{d(N)}(t)/N$, $\mathcal S$ carries the $\ell_1$ topology, and the initial states are deterministic with $\|\mathbf q^{d(N)}(0)-\mathbf q^\infty\|_1\to0$, $\mathbf q^\infty\in\mathcal S$. The rate $\lambda=0$ is allowed. Sampling is without replacement, so $d(N)=N$ is the ordinary JSQ policy. Weak convergence to a continuous limit is rendered in coupling form, and the existence of the limit is part of the conclusion.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 5, Theorem 2.1, (2.1)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Theorem 2.1** (p. 5, universality of the fluid limit for JSQ(d(N))). The `j`-th system has
`N = j + 1` servers, buffer `b ≥ 1`, arrival rate `λ_j ≥ 0` with `λ_j / N → λ ∈ [0, 1)`, and
uses JSQ(`d_j`) with `1 ≤ d_j ≤ N` and `d_j → ∞`. Its initial occupancy vector `Q0 j` is
deterministic and `q^{d(N)}(0) = Q0 j / N → q^∞ ∈ 𝕊` in `ℓ¹`. Then any subsequence of the
fluid-scaled processes `q^{d(N)}` has a further subsequence converging weakly (Skorohod `J₁`,
`ℓ¹` topology) to a limit satisfying the integral equations (2.1). -/
theorem theorem_2_1 (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (lamN : ℕ → ℝ) (hlamN : ∀ j, 0 ≤ lamN j)
    (hlim : Tendsto (fun j => lamN j / ((j : ℝ) + 1)) atTop (𝓝 lam))
    (d : ℕ → ℕ) (hd : ∀ j, 1 ≤ d j ∧ d j ≤ j + 1) (hdinf : Tendsto d atTop atTop)
    (qinf : ℕ → ℝ) (hqinf : qinf ∈ FluidSpace b) (Q0 : ℕ → ℕ →₀ ℕ)
    (hQ0 : Tendsto (fun j => l1dist (scaledOcc (j + 1) (Q0 j)) qinf) atTop (𝓝 0))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sys : ∀ j, System P (j + 1) b (lamN j)) (hsys : ∀ j ω, (sys j).Q0 ω = Q0 j) :
    SubseqFluidLimit P b lam qinf (fun j ω t => (sys j).fluid (jsqd (j + 1) (d j)) ω t) := by sorry

end PowerOfDUniversality.Fluid
