-- Prove2me | Theorems.Thm_StrictCompatLB_FullInhomogeneous_jsqd_kernel_stochastic_and_uniformized_law
-- name    : StrictCompatLB.FullInhomogeneous.jsqd_kernel_stochastic_and_uniformized_law
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T21:14:48.475322+00:00
-- url     : https://prove2.me/theorems/bef6073e-ce16-4d17-92fc-458c7a34d7ed
-- title:
--   On a connected compatibility graph the JSQ($d$) kernel is stochastic and every initial law has a uniformized chain at rate $(\lambda+1)N$
-- statement:
--   Let $\lambda\ge 0$, $d\ge 1$, and let $G_N$ be a bipartite compatibility graph between $N\ge 1$ servers and $M(N)\ge 1$ dispatchers that is connected. Then the one-step jump kernel $K$ of the uniformized JSQ($d$) queue-length chain on $\mathbb{N}^N$ (arrivals at rate $\lambda N$ routed by each dispatcher to a shortest queue among $d$ sampled compatible servers, departures at rate 1 per busy server, uniformized at total rate $(\lambda+1)N$) is a stochastic kernel, and for every initial probability vector $\mu$ on $\mathbb{N}^N$ there is a probability measure on paths $\times$ clocks under which the jump chain is Markov with kernel $K$ and initial law $\mu$, the clock gaps are i.i.d. exponential with rate $(\lambda+1)N$ independent of the chain, and the jump times do not accumulate.
--
--   Role: the well-posedness conjuncts of Theorem 3.6 (the kernel is stochastic and the Markov process exists for every initial law) for every $N$ beyond the connectivity threshold.
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Section 2 (model) and Theorem 3.6, p. 13; construction of the uniformized chain: J. R. Norris, Markov Chains (Cambridge 1997), Section 2.6 and Theorem 2.7.1

import Mathlib
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
import Definitions.Def_StrictCompatLB_MeanField_Model
import Definitions.Def_StrictCompatLB_FullInhomogeneous_UniformizedLaw
import Definitions.Def_StrictCompatLB_FullInhomogeneous_Trajectory

open MeasureTheory Filter Topology
open StrictCompatLB.MeanField StrictCompatLB.Inhomogeneous
open scoped ENNReal NNReal

namespace StrictCompatLB.FullInhomogeneous

theorem jsqd_kernel_stochastic_and_uniformized_law : ∀ (lam : ℝ), 0 ≤ lam → ∀ (d : ℕ), 1 ≤ d →
    ∀ (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ), 1 ≤ N → 0 < M N →
    (compatGraph M G N).Connected →
    IsStochasticKernel (jsqdKernel lam d M G N) ∧
      ∀ μ : (Fin N → ℕ) → ℝ, IsProbVec μ →
        ∃ P : Measure (ChainSample (Fin N → ℕ)),
          IsUniformizedLaw P (jsqdKernel lam d M G N) ((lam + 1) * (N : ℝ)) μ := by sorry

end StrictCompatLB.FullInhomogeneous
