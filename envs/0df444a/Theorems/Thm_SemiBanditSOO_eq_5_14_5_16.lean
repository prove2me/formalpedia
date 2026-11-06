-- Prove2me | Theorems.Thm_SemiBanditSOO_eq_5_14_5_16
-- name    : SemiBanditSOO.eq_5_14_5_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:36.452227+00:00
-- url     : https://prove2.me/theorems/c177688a-ffd4-453e-ad20-371a7253b3f4
-- title:
--   (5.14)–(5.16) — $W\le T$, (5.15), $\Delta\le24\sqrt{S\Lambda'W}+417S\Lambda(1+\log T)$, and $\sum_t\mathbb E[\mathbf 1_{G_t}\mathrm{Reg}_t]\le\Delta\le24\sqrt{ST\Lambda'}+\dots$
-- statement:
--   Assume Assumption 3.1 and $S=\sum_i\min\{s_i,k_i\}<\infty$. Let $\delta\in(0,1)$, $\Lambda=\log(80n(T+1)^3/\delta)$ and $\Lambda'=\Lambda\log T(1+\log T)$. Let $G_t$ be the good event of round $t$, $d_{t,h}$ and $w_{t,h}$ the gap and the conditional variance of stage $h$ of round $t$, and
--   $$\Delta=\sum_{t=1}^T\mathbb E\Bigl[\mathbf 1_{G_t}\sum_h d_{t,h}\Bigr],\qquad W=\sum_{t=1}^T\mathbb E\Bigl[\mathbf 1_{G_t}\sum_h w_{t,h}\Bigr].$$
--   Let $\bar s_i=\min\{s_i,k_i\}$, let $I_{i,t}$ indicate that coordinate $i$ is revealed on an edge in round $t$, and let $\widetilde w_{i,t}$ be $w_{t,h}$ at the stage $h$ revealing $i$ ($0$ if there is none). Algorithm 1 satisfies
--   $$W\le\sum_{t=1}^T\mathbb P(G_t)\le T, \qquad (5.14)$$
--   $$\mathbb E\Bigl[\sum_{t,i}\mathbf 1_{G_t}I_{i,t}\sqrt{\frac{\bar s_i\widetilde w_{i,t}}{N_{i,t}+1}}\Bigr]\le\sqrt{S(1+\log T)W}, \qquad (5.15)$$
--   $$\Delta\le24\sqrt{S\Lambda'W}+417S\Lambda(1+\log T), \qquad (5.16)$$
--   and, in conclusion,
--   $$\sum_{t=1}^T\mathbb E[\mathbf 1_{G_t}\mathrm{Reg}_t]\le\Delta\le24\sqrt{ST\Lambda'}+417S\Lambda(1+\log T).$$
--
--   Together with (5.8) this proves Theorem 3.2 with $c=417$.
--
--   **Formalization Note.** The displays (5.15) and (5.16) are stated from their first to their last member; their intermediate members are applications of the Cauchy–Schwarz inequality and of (5.12)–(5.13). All expectations of indicator terms are lower Lebesgue integrals.
--
--   Differences from the source:
--   - generalization: a finite rooted decision tree → a finite rooted DAG (every node reachable from the root, a height function strictly decreasing along edges); reason: footnote 1 (p.6) states that the analysis applies to such DAGs since obs(u) is a function of the node; a tree is an instance
--   - encoding: partial observation vectors x_obs(u) → full vectors x : (i : Fin n) → dom i, with feasibility, rewards and policies required to depend only on the coordinates in obs(u); reason: Lean convention; the same problems
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - encoding: OPT(D) = sup over (possibly randomized) policies → sup over measurable deterministic policies; reason: a randomized policy is a distribution over deterministic ones, so its value is an average of deterministic values and the supremum is the same
--   - encoding: ties in (3.5) broken in a fixed order → least maximizer for an arbitrary linear order on the node type (the statement holds for every order); reason: a fixed order is a linear order on the nodes
--   - encoding: Algorithm 1 run on T i.i.d. rounds X^1, …, X^T ∼ D, rounds t = 1, …, T → a deterministic function of ω = (X^1, …, X^T) under the product measure, rounds numbered 0, …, T − 1; reason: Algorithm 1 has no internal randomness; the same run
--   - generalization: Assumption 3.1 for all nonempty families 𝒫_1, …, 𝒫_n → Assumption 3.1 only for families whose optimistic DP is measurable (MeasurableDP); reason: a weaker hypothesis; the proof applies the assumption only to the confidence sets of Algorithm 1, whose DP is measurable by the paper's assumption (p.10), and it keeps every expectation a genuine integral
--   - generalization: the optimistic values are measurable in the samples and observations (p.10) → ḡ^t_u and h̄^t_(u,v) jointly measurable in the history ω and the observations, for t < T (StandingMeasurable); reason: a weaker hypothesis: the samples are measurable functions of the history, so the paper's assumption implies it; it holds automatically for finite domains
--   - encoding: s_i, k_i ∈ ℤ_{>0} ∪ {∞}, S = Σ_i min{s_i, k_i} finite → s_i, k_i, S ∈ ℕ∞ with 1 ≤ s_i, k_i = supportCount D_i, S ≠ ⊤, and S cast to ℝ; reason: Lean convention; the same values
--   - encoding: n random variables X_1, …, X_n → hypothesis 1 ≤ n; reason: Λ = log(80n(T + 1)³/δ) is defined only for n ≥ 1; n = 0 is not a problem of the paper
--   - encoding: T rounds → T : ℕ with 1 ≤ T; reason: the number of rounds is a positive integer
--   - encoding: 𝔼[1_{G_t} Reg_t] → lower Lebesgue integral of 1_{G_t} · ofReal(Reg_t) (goodRegret); reason: Reg_t ≥ 0 and is bounded; no measurability of G_t needs to be proved
--   - encoding: Δ, W and the left-hand side of (5.15), expectations of real quantities → goodGap, goodVar and goodRootSum, lower Lebesgue integrals of ofReal in ℝ≥0∞, with W entering real bounds through toReal, and the real bounds through ofReal; reason: the integrands are nonnegative on G_t and W ≤ T, so the values and the inequalities are the same; no measurability of G_t needs to be proved
--   - encoding: d_{t,h}, w_{t,h} = conditional gap and variance of stage h, and w̃_{i,t} = w_{t,h} at the stage revealing i → the paper's explicit expressions (p.25) summed along the path of σ^t on X^t (pathSum); revealVar is that sum restricted to edges revealing i; reason: the paper identifies the two; a coordinate is revealed at most once per round, so the restricted sum has at most one nonzero term
--   - encoding: the chains of inequalities (5.15) and (5.16) → their first and last members; reason: the intermediate members are one-line applications of the Cauchy–Schwarz inequality and of (5.12)–(5.13) inside the derivation, with no use outside it
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, proof of Theorem 3.2, (5.14)–(5.16), pp.25–26

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet
import Definitions.Def_SemiBanditSOO_OptimisticDP
import Definitions.Def_SemiBanditSOO_Algorithm

open MeasureTheory

namespace SemiBanditSOO

/-- **(5.14)–(5.16): the regret of good rounds.** Harada, Kawase, Sumita, *Beyond Monotonicity:
Stochastic Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, proof of
Theorem 3.2, (5.14)–(5.16), pp.25–26.

Under Assumption 3.1, with `S = Σ_i min{s_i, k_i}` finite, `Λ = log(80 n (T + 1)³/δ)`,
`Λ' = Λ log T (1 + log T)`, and with `Δ = Σ_t 𝔼[1_{G_t} Σ_h d_{t,h}]`, `W = Σ_t 𝔼[1_{G_t} Σ_h w_{t,h}]`,
Algorithm 1 satisfies
* (5.14): `W ≤ Σ_t ℙ(G_t) ≤ T`;
* (5.15): `𝔼[Σ_{t,i} 1_{G_t} I_{i,t} √(s̄_i w̃_{i,t}/(N_{i,t} + 1))] ≤ √(S (1 + log T) W)`;
* (5.16): `Δ ≤ 24 √(S Λ' W) + 417 S Λ (1 + log T)`;
* the concluding line of the proof, p.26: `Σ_t 𝔼[1_{G_t} Reg_t] ≤ Δ ≤ 24 √(S T Λ') + 417 S Λ (1 + log T)`.

**Formalization Note.** `Δ`, `W` and the left-hand side of (5.15) are `goodGap`, `goodVar` and
`goodRootSum`; like `𝔼[1_{G_t} Reg_t]` (`goodRegret`) they are lower Lebesgue integrals in `ℝ≥0∞`, and
`W` enters a real bound through `toReal` (it is at most `T`). (5.15) and (5.16) are stated from their
first to their last member; the intermediate members are single applications of the Cauchy–Schwarz
inequality and of (5.12)–(5.13). `S ∈ ℕ∞` is cast to `ℝ` after `S ≠ ⊤`. The standing measurability
assumption (p.10) is a hypothesis. -/
theorem eq_5_14_5_16 {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} [Fintype V] [LinearOrder V]
    (Pb : Problem n dom V) (D : ∀ i, ProbabilityMeasure (dom i)) (s : Fin n → ℕ∞)
    (T : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hs : ∀ i, 1 ≤ s i) (hA : Pb.Assumption31 s)
    (hS : totalCpx s D ≠ ⊤) (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hmeas : Pb.StandingMeasurable T δ) :
    (Pb.goodVar D T δ ≤ ∑ t : Fin T, roundsMeasure D T (Pb.goodEvent D T δ t) ∧
      ∑ t : Fin T, roundsMeasure D T (Pb.goodEvent D T δ t) ≤ (T : ENNReal)) ∧
    Pb.goodRootSum D s T δ ≤
      ENNReal.ofReal (Real.sqrt (((totalCpx s D).toNat : ℝ) * (1 + Real.log T) *
        (Pb.goodVar D T δ).toReal)) ∧
    Pb.goodGap D T δ ≤
      ENNReal.ofReal (24 * Real.sqrt (((totalCpx s D).toNat : ℝ) *
            (Lam n T δ * Real.log T * (1 + Real.log T)) * (Pb.goodVar D T δ).toReal) +
        417 * ((totalCpx s D).toNat : ℝ) * Lam n T δ * (1 + Real.log T)) ∧
    ∑ t : Fin T, Pb.goodRegret D T δ t ≤ Pb.goodGap D T δ ∧
    Pb.goodGap D T δ ≤
      ENNReal.ofReal (24 * Real.sqrt (((totalCpx s D).toNat : ℝ) * T *
            (Lam n T δ * Real.log T * (1 + Real.log T))) +
        417 * ((totalCpx s D).toNat : ℝ) * Lam n T δ * (1 + Real.log T)) := by sorry

end SemiBanditSOO
