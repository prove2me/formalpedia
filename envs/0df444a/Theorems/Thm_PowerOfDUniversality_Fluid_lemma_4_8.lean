-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_lemma_4_8
-- name    : PowerOfDUniversality.Fluid.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:39.332986+00:00
-- url     : https://prove2.me/theorems/71c46cf8-13fc-49cf-8184-03b3775b87f7
-- title:
--   Lemma 4.8 — under JSQ, w.h.p. no task joins a server with M(t, q^∞) − 1 tasks before time t
-- statement:
--   Consider the ordinary JSQ policy in systems with $N_j\ge1$ servers, $N_j\to\infty$, buffer $b\ge 1$ and arrival rates $\lambda_j\ge0$ with $\lambda_j/N_j\to\lambda>0$, and assume $\mathbf q^{N_j}(0)\xrightarrow{\mathcal L}\mathbf q^\infty\in\mathcal S$ in $\ell_1$. Then for every $t\ge0$ there exists $M=M(t,\mathbf q^\infty)\ge1$ such that, with probability tending to one as $j\to\infty$, no arriving task is assigned to a server with $M-1$ active tasks during $[0,t]$:
--   $$\lim_{j\to\infty}\mathbb P\big(A^{N_j}_M(t)=0\big)=1,$$
--   where $A_M(t)$ counts the arrivals in $[0,t]$ assigned to a server with $M-1$ tasks.
--
--   The lemma confines the JSQ dynamics on $[0,t]$ to the first $M$ levels, which gives the compact containment needed for relative compactness.
--
--   **Formalization Note** The printed "for any $\mathbf q\in\mathcal S$" refers to $\mathbf q^\infty$. Convergence in distribution to a deterministic limit is stated as convergence in probability. The standing assumptions of §4.1 (those of Theorem 4.1) are hypotheses. $M$ is chosen after $t$ and before the sequence of systems, so it depends only on $t$, $\mathbf q^\infty$ and the fixed parameters $b,\lambda$, as the paper's explicit choice $M(t,\mathbf q^\infty)=\min\{k\ge1:\sum_{i=1}^{k-1}(1-q^\infty_i)>\lambda t\}$ does.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 22, Lemma 4.8

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Lemma 4.8** (p. 22), under the standing assumptions of Theorem 4.1 (buffer `b ≥ 1`,
`λ_j / N_j → λ > 0`, `N_j → ∞` servers, ordinary JSQ) and `q^{N_j}(0) → q^∞ ∈ 𝕊` in distribution
(equivalently in probability, the limit being deterministic) in `ℓ¹`. For every `t ≥ 0` there is
`M = M(t, q^∞) ≥ 1`, chosen before (and independently of) the sequence of systems, such that
with probability tending to one no arriving task is assigned to a server with `M − 1` active
tasks up to time `t`: `P(A^{N_j}_M(t) = 0) → 1`. -/
theorem lemma_4_8 (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam : 0 < lam)
    (qinf : ℕ → ℝ) (hqinf : qinf ∈ FluidSpace b) :
    ∀ t : ℝ, 0 ≤ t → ∃ M : ℕ, 1 ≤ M ∧
      ∀ (Ns : ℕ → ℕ) (lamN : ℕ → ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (sys : ∀ j, System P (Ns j) b (lamN j)),
        (∀ j, 1 ≤ Ns j) → Tendsto Ns atTop atTop → (∀ j, 0 ≤ lamN j) →
        Tendsto (fun j => lamN j / (Ns j : ℝ)) atTop (𝓝 lam) →
        (∀ ε : ℝ, 0 < ε → Tendsto (fun j => P {ω | ENNReal.ofReal ε ≤
          l1dist (scaledOcc (Ns j) ((sys j).Q0 ω)) qinf}) atTop (𝓝 0)) →
        Tendsto (fun j => P {ω | (sys j).arrivalsTo jsq ω t M = 0}) atTop (𝓝 1) := by sorry

end PowerOfDUniversality.Fluid
