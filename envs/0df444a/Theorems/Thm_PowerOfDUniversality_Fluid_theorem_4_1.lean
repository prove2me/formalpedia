-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_theorem_4_1
-- name    : PowerOfDUniversality.Fluid.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:50.028391+00:00
-- url     : https://prove2.me/theorems/9ab62529-d501-4bcf-98cc-71ff5563ac4b
-- title:
--   Theorem 4.1 — fluid limit of JSQ in ℓ¹: subsequential weak limits solve (4.5)
-- statement:
--   Consider the ordinary JSQ policy in systems with $N_j\ge1$ servers, $N_j\to\infty$, a buffer $b\ge1$ and arrival rates $\lambda_j\ge0$ with $\lambda_j/N_j\to\lambda>0$. Assume that the fluid-scaled initial states satisfy $\mathbf q^{N_j}(0)\xrightarrow{\mathbb P}\mathbf q^\infty$ in $\mathcal S$ (in the $\ell_1$ distance). Then any subsequence of the processes $\{\mathbf q^{N_j}(t)\}_{t\ge0}$ has a further subsequence that converges weakly with respect to the Skorohod $J_1$ topology to a limit $\{\mathbf q(t)\}_{t\ge0}$ satisfying
--   $$q_i(t)=q_i(0)+\lambda\int_0^t p_{i-1}(\mathbf q(s))\,ds-\int_0^t\big(q_i(s)-q_{i+1}(s)\big)\,ds,\qquad i=1,2,\dots,b, \tag{4.5}$$
--   where $\mathbf q(0)=\mathbf q^\infty$ and the coefficients $p_i$ are those of (4.4).
--
--   This is the transient fluid limit of JSQ on the space $\mathcal S$ with the $\ell_1$ topology; the universality result for JSQ($d(N)$) is reduced to it.
--
--   **Formalization Note** The servers counts form an arbitrary sequence $N_j\to\infty$ (Proposition 4.9 applies the theorem to $N-n(N)$ servers). There is no restriction $\lambda<1$. The initial states are random, independent of the arrival and service randomness. Weak convergence to a continuous limit is rendered in coupling form (copies converging almost surely uniformly on compacts in $\ell_1$), and the existence of the limit is part of the conclusion.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 17, Theorem 4.1, (4.4), (4.5)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Theorem 4.1** (p. 17, fluid limit of JSQ). Systems `j = 0, 1, …` with `N_j ≥ 1` servers
(`N_j → ∞`), buffer `b ≥ 1` and arrival rates `λ_j ≥ 0` with `λ_j / N_j → λ > 0` run the ordinary
JSQ policy from random initial occupancy vectors with `q^{N_j}(0) → q^∞ ∈ 𝕊` in probability in
`ℓ¹`. Then any subsequence of the fluid-scaled processes `q^{N_j}` has a further subsequence
converging weakly (Skorohod `J₁`, `ℓ¹` topology) to a limit satisfying (4.5) with
`q(0) = q^∞` and the coefficients (4.4). -/
theorem theorem_4_1 (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam : 0 < lam)
    (Ns : ℕ → ℕ) (hNs1 : ∀ j, 1 ≤ Ns j) (hNs : Tendsto Ns atTop atTop)
    (lamN : ℕ → ℝ) (hlamN : ∀ j, 0 ≤ lamN j)
    (hlim : Tendsto (fun j => lamN j / (Ns j : ℝ)) atTop (𝓝 lam))
    (qinf : ℕ → ℝ) (hqinf : qinf ∈ FluidSpace b)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sys : ∀ j, System P (Ns j) b (lamN j))
    (hinit : ∀ ε : ℝ, 0 < ε → Tendsto (fun j => P {ω | ENNReal.ofReal ε ≤
      l1dist (scaledOcc (Ns j) ((sys j).Q0 ω)) qinf}) atTop (𝓝 0)) :
    SubseqFluidLimit P b lam qinf (fun j ω t => (sys j).fluid jsq ω t) := by sorry

end PowerOfDUniversality.Fluid
