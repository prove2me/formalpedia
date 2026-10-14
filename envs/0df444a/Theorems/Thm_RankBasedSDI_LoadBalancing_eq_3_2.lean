-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_eq_3_2
-- name    : RankBasedSDI.LoadBalancing.eq_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:38.503866+00:00
-- url     : https://prove2.me/theorems/362590fb-e7b6-4f54-954a-a3e8b402a2ec
-- title:
--   (3.2): monotonicity of the rank-based drift sets for nonincreasing $b$
-- statement:
--   Let $b\in\mathbb R^N$ be nonincreasing, $b_1\ge b_2\ge\dots\ge b_N$. Let $x,y\in\mathbb R^N$ and let $\beta\in\mathrm{conv}\{b_\pi:\pi\in\mathfrak P(x)\}$ and $\gamma\in\mathrm{conv}\{b_\pi:\pi\in\mathfrak P(y)\}$. Then
--
--   $$
--   \sum_{i=1}^N(x_i-y_i)(\beta_i-\gamma_i)\le0 .
--   $$
--
--   In the paper this is display (3.2) in the proof of Proposition 3.1, stated along two solutions $X,Y$ with drifts $\beta,\gamma$ for a.e. $t$. It is the monotonicity property of the set-valued drift on which pathwise uniqueness of (SDI) and (SDIR) rests.
--
--   **Formalization Note** The statement is the pointwise, deterministic form that pp. 9–10 prove at each fixed time. The a.e.-$t$ form follows by applying it at every $t$ where both inclusions hold. "Nonincreasing" is `Antitone b` on `Fin N`.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 9, Proof of Proposition 3.1, (3.2) (argued pp. 9–10); hypothesis on b from Theorem 2.2, p. 8

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Rank
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy

namespace RankBasedSDI.LoadBalancing

theorem eq_3_2 {N : ℕ} (b : Fin N → ℝ) (hb : Antitone b) (x y β γ : Fin N → ℝ)
    (hβ : β ∈ driftSet b x) (hγ : γ ∈ driftSet b y) :
    ∑ i, (x i - y i) * (β i - γ i) ≤ 0 := by sorry

end RankBasedSDI.LoadBalancing
