-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_proposition_3_1
-- name    : RankBasedSDI.LoadBalancing.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:03.472126+00:00
-- url     : https://prove2.me/theorems/e2f371af-5cc1-4a74-a204-38d72c00729f
-- title:
--   Proposition 3.1: pathwise uniqueness for (SDI) and (SDIR)
-- statement:
--   Let data $b,m\in\mathbb R^N$, $\sigma\in(0,\infty)^N$ be given and assume that $b$ is nonincreasing (the standing hypothesis of Theorem 2.2, which §3 proves). Then pathwise uniqueness holds for (SDI) and for (SDIR).
--
--   For (SDIR) this means the following. Let $(X,L,B)$ and $(\tilde X,\tilde L,B)$ be weak solutions, with drift processes $\beta,\tilde\beta$, on a common stochastic basis, driven by the same Brownian motion, and with $X(0)=\tilde X(0)$ a.s. Then almost surely
--
--   $$
--   X(t)=\tilde X(t)\quad\text{and}\quad L(t)=\tilde L(t)\qquad\text{for all } t\ge0 .
--   $$
--
--   For (SDI) the conclusion is the indistinguishability of $X$ and $\tilde X$.
--
--   Together with weak existence, pathwise uniqueness gives uniqueness in law (Remark 2.1, Yamada–Watanabe), which turns subsequential convergence of the queueing model into convergence of the whole sequence.
--
--   **Formalization Note** The statement is the conjunction `PathwiseUniqueSDIR b m σ ∧ PathwiseUniqueSDI b m σ`. Stochastic bases range over `Ω : Type`. The definition of pathwise uniqueness (p. 7) includes "and so are $L$ and $\tilde L$", and it is kept here.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 9, Proposition 3.1 (hypotheses from Theorem 2.2, p. 8; definitions p. 7)

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

theorem proposition_3_1 {N : ℕ} (b m σ : Fin N → ℝ) (hb : Antitone b)
    (hσ : ∀ i, 0 < σ i) :
    PathwiseUniqueSDIR b m σ ∧ PathwiseUniqueSDI b m σ := by sorry

end RankBasedSDI.LoadBalancing
