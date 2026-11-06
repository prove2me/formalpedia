-- Prove2me | Theorems.Thm_SemiBanditSOO_eq_5_8
-- name    : SemiBanditSOO.eq_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:03.196453+00:00
-- url     : https://prove2.me/theorems/1f20c02f-872b-40c0-b6b2-6f1ec3a1eb8c
-- title:
--   (5.8) — $R_T=\sum_t\mathbb E[\mathrm{Reg}_t]\le\sum_t\mathbb E[\mathbf 1_{G_t}\mathrm{Reg}_t]+\delta T$
-- statement:
--   Consider Algorithm 1 with input $\delta\in(0,1)$, and let $G_t$ be the event that $D_i\in\mathcal C_{i,t}$ for every $i\in[n]$. Then
--   $$R_T=\sum_{t=1}^T\mathbb E[\mathrm{Reg}_t]\le\sum_{t=1}^T\mathbb E[\mathbf 1_{G_t}\mathrm{Reg}_t]+\delta T, \qquad (5.8)$$
--   where $\mathrm{Reg}_t=\mathrm{OPT}(D)-f(\sigma^t\mid D)$ is the expected regret of the policy of round $t$, a function of the history before round $t$.
--
--   This reduces the regret to the good rounds, in which the confidence sets contain the true distributions.
--
--   **Formalization Note.** Both the identity and the inequality of the display are stated; the inequality is stated in $[0,\infty]$, where both sides are finite.
--
--   Differences from the source:
--   - generalization: a finite rooted decision tree → a finite rooted DAG (every node reachable from the root, a height function strictly decreasing along edges); reason: footnote 1 (p.6) states that the analysis applies to such DAGs since obs(u) is a function of the node; a tree is an instance
--   - encoding: partial observation vectors x_obs(u) → full vectors x : (i : Fin n) → dom i, with feasibility, rewards and policies required to depend only on the coordinates in obs(u); reason: Lean convention; the same problems
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - encoding: OPT(D) = sup over (possibly randomized) policies → sup over measurable deterministic policies; reason: a randomized policy is a distribution over deterministic ones, so its value is an average of deterministic values and the supremum is the same
--   - encoding: ties in (3.5) broken in a fixed order → least maximizer for an arbitrary linear order on the node type (the statement holds for every order); reason: a fixed order is a linear order on the nodes
--   - encoding: Algorithm 1 run on T i.i.d. rounds X^1, …, X^T ∼ D, rounds t = 1, …, T → a deterministic function of ω = (X^1, …, X^T) under the product measure, rounds numbered 0, …, T − 1; reason: Algorithm 1 has no internal randomness; the same run
--   - generalization: the optimistic values are measurable in the samples and observations (p.10) → ḡ^t_u and h̄^t_(u,v) jointly measurable in the history ω and the observations, for t < T (StandingMeasurable); reason: a weaker hypothesis: the samples are measurable functions of the history, so the paper's assumption implies it; it holds automatically for finite domains
--   - encoding: n random variables X_1, …, X_n → hypothesis 1 ≤ n; reason: Λ = log(80n(T + 1)³/δ) is defined only for n ≥ 1; n = 0 is not a problem of the paper
--   - encoding: T rounds → T : ℕ with 1 ≤ T; reason: the number of rounds is a positive integer
--   - encoding: 𝔼[1_{G_t} Reg_t] → lower Lebesgue integral of 1_{G_t} · ofReal(Reg_t) (goodRegret); reason: Reg_t ≥ 0 and is bounded; no measurability of G_t needs to be proved
--   - encoding: the real inequality R_T ≤ Σ_t 𝔼[1_{G_t} Reg_t] + δT → the inequality in ℝ≥0∞, with ofReal on R_T and on δT; reason: R_T ≥ 0 and both sides are finite, so the two inequalities are the same
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, proof of Theorem 3.2, (5.8), p.24

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet
import Definitions.Def_SemiBanditSOO_OptimisticDP
import Definitions.Def_SemiBanditSOO_Algorithm

open MeasureTheory

namespace SemiBanditSOO

/-- **(5.8): bad rounds cost at most `δT`.** Harada, Kawase, Sumita, *Beyond Monotonicity:
Stochastic Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, proof of
Theorem 3.2, (5.8), p.24.

Let `G_t` be the event that `D_i ∈ 𝒞_{i,t}` for every `i ∈ [n]`. For Algorithm 1 with input
`δ ∈ (0, 1)`,
`R_T = Σ_{t=1}^T 𝔼[Reg_t] ≤ Σ_{t=1}^T 𝔼[1_{G_t} Reg_t] + δT`,
where `Reg_t = OPT(D) − f(σ^t | D)`.

**Formalization Note.** Both relations of the display are stated: the identity
`R_T = Σ_t 𝔼[Reg_t]` (with `Reg_t` a function of the history before round `t`) and the
inequality. `𝔼[1_{G_t} Reg_t]` is the lower Lebesgue integral `goodRegret`; the inequality is
stated in `ℝ≥0∞` through `ofReal` (both sides are finite). The standing measurability assumption
(p.10) is a hypothesis. -/
theorem eq_5_8 {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} [Fintype V] [LinearOrder V]
    (Pb : Problem n dom V) (D : ∀ i, ProbabilityMeasure (dom i)) (T : ℕ) (δ : ℝ)
    (hn : 1 ≤ n) (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hmeas : Pb.StandingMeasurable T δ) :
    Pb.regret D T δ = ∑ t : Fin T, ∫ ω, Pb.roundRegret D T δ ω t ∂(roundsMeasure D T) ∧
    ENNReal.ofReal (Pb.regret D T δ) ≤
      ∑ t : Fin T, Pb.goodRegret D T δ t + ENNReal.ofReal (δ * T) := by sorry

end SemiBanditSOO
