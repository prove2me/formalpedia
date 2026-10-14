-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_eq_5_15
-- name    : RankBasedSDI.LoadBalancing.eq_5_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:06.965143+00:00
-- url     : https://prove2.me/theorems/d387d90c-084e-4b2d-a5da-ddbefb3cdec7
-- title:
--   (5.15): coordinates of an (SDIR) solution meet on a Lebesgue-null set of times, so it solves (SDER)
-- statement:
--   Let data $b,m\in\mathbb R^N$ and $\sigma\in(0,\infty)^N$ be given, and let $(X,L,B)$ with drift $\beta$ be a weak solution of (SDIR). Then:
--
--   1. almost surely, for all $i\ne j$ and all $t\ge0$,
--
--   $$
--   \int_0^t1_{\{X_i(u)=X_j(u)\}}\,du=0 ,
--   $$
--
--   i.e. the set of times at which two components meet has Lebesgue measure zero;
--   2. $(X,L,B)$ is a weak solution of (SDER).
--
--   Since $\mathfrak P(x)$ is a single permutation (the rank permutation) when the coordinates of $x$ are distinct, the inclusion forces $\beta(t)=b_{\mathcal R(t)}$ for a.e. $t$. This is the step from (SDIR) to (SDER) in the proof of Theorem 2.3.
--
--   **Formalization Note** No monotonicity of $b$ is assumed; the paper's argument does not use it. The (SDI)/(SDE) analogue ("handled in a similar manner") is not included. The measure is Lebesgue measure of $\{u\in[0,t]:X_i(u)=X_j(u)\}$.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 17, Proof of Theorem 2.3, (5.15) and the two sentences after it

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Rank
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_RankBasedSDI_LoadBalancing_RankBasedEquations
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy

namespace RankBasedSDI.LoadBalancing

theorem eq_5_15 {N : ℕ} (b m σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (X L B β : Ω → ℝ → Fin N → ℝ) (h : IsWeakSolutionSDIR b m σ P F X L B β) :
    (∀ᵐ ω ∂P, ∀ i j : Fin N, i ≠ j → ∀ t : ℝ, 0 ≤ t →
      volume {u : ℝ | u ∈ Set.Icc 0 t ∧ X ω u i = X ω u j} = 0) ∧
    IsWeakSolutionSDER b m σ P F X L B := by sorry

end RankBasedSDI.LoadBalancing
