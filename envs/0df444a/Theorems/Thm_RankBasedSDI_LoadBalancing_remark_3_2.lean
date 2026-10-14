-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_remark_3_2
-- name    : RankBasedSDI.LoadBalancing.remark_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:18.31332+00:00
-- url     : https://prove2.me/theorems/2632628e-640e-43bd-8493-684be8476512
-- title:
--   Remark 3.2: every solution of (SDE) solves (SDI), and every solution of (SDER) solves (SDIR)
-- statement:
--   Let data $b,m,\sigma\in\mathbb R^N$ be given. On a stochastic basis $(\Omega,\mathcal F,\mathbb F,P)$:
--
--   1. if $(X,B)$ is a weak solution of (SDE), then $(X,B)$ is a weak solution of (SDI) with drift $\beta(t)=(b_{\mathcal R_1(t)},\dots,b_{\mathcal R_N(t)})$, $\mathcal R_i(t)=\mathrm{rank}(i;X(t))$;
--   2. if $(X,L,B)$ is a weak solution of (SDER), then $(X,L,B)$ is a weak solution of (SDIR) with the same drift $\beta$.
--
--   Both parts rest on two facts. The rank permutation $i\mapsto\mathrm{rank}(i;x)$ belongs to $\mathfrak P(x)$, so $(b_{\mathrm{rank}(i;x)})_i$ lies in $\mathrm{conv}\{b_\pi:\pi\in\mathfrak P(x)\}$. And $t\mapsto b_{\mathcal R(t)}$ is progressively measurable.
--
--   **Formalization Note** The remark's third sentence ("Hence, the above immediately gives the pathwise uniqueness to (SDE) and (SDER)") is not formalized; only the first two sentences are. The drift is `rankDrift b (X ω t)`.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 9, Remark 3.2 (first two sentences)

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

theorem remark_3_2 {N : ℕ} (b m σ : Fin N → ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (X L B : Ω → ℝ → Fin N → ℝ) :
    (IsWeakSolutionSDE b m σ P F X B →
      IsWeakSolutionSDI b m σ P F X B (fun ω t => rankDrift b (X ω t))) ∧
    (IsWeakSolutionSDER b m σ P F X L B →
      IsWeakSolutionSDIR b m σ P F X L B (fun ω t => rankDrift b (X ω t))) := by sorry

end RankBasedSDI.LoadBalancing
