-- Prove2me | Theorems.Thm_SemiBanditSOO_eq_5_12
-- name    : SemiBanditSOO.eq_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:40.664187+00:00
-- url     : https://prove2.me/theorems/25d29841-cb60-46ac-90ce-c94b60f88d08
-- title:
--   (5.12) — $0\le d_{t,h}\le24\sqrt{\frac{\bar s_i\Lambda\log T}{N_{i,t}+1}w_{t,h}}+\frac{417\bar s_i\Lambda}{N_{i,t}+1}$
-- statement:
--   Assume Assumption 3.1, and let $\bar s_i=\min\{s_i,k_i\}$ with $k_i$ the number of support points of $D_i$, finite. Consider a round with samples $Z_{j,1},\dots,Z_{j,N_j}$ of each coordinate $j$, in which $D_j\in\mathcal C_{N_j}(\widehat D_{j,N_j})$ for every $j$, and an edge $(u,v)$ revealing coordinate $i$ with $v\in\mathcal A_u(x_{\mathrm{obs}(u)})$, where $N_i+1\le T$. With $d$ and $w$ the gap and the variance of this stage for the confidence sets,
--   $$0\le d\le24\sqrt{\frac{\bar s_i\Lambda\log T}{N_i+1}w}+\frac{417\bar s_i\Lambda}{N_i+1}. \qquad (5.12)$$
--
--   This is the per-stage bound that, summed over rounds, gives the $\sqrt{ST}$ regret.
--
--   **Formalization Note.** $\Lambda=\log(80n(T+1)^3/\delta)$; the confidence sets' optimistic DP is assumed measurable, as in the paper.
--
--   Differences from the source:
--   - generalization: the edge chosen by (3.5) at a stage h < h* of a good round t, with the samples of round t → every feasible edge revealing i, and arbitrary sample lists L with D_j ∈ 𝒞(L_j) for all j and |L_i| + 1 ≤ T; reason: the argument (Lemma 5.4(b) or 5.5 with P = D_i) uses only these facts; the stages of Algorithm 1 are instances, since N_{i,t} ≤ T − 1
--   - encoding: s̄_i = min{s_i, k_i} (finite since S < ∞) → hypothesis min(s_i, supportCount D_i) ≠ ⊤, cast to ℝ; reason: S < ∞ in Theorem 3.2 makes every s̄_i finite
--   - generalization: a finite rooted decision tree → a finite rooted DAG (every node reachable from the root, a height function strictly decreasing along edges); reason: footnote 1 (p.6) states that the analysis applies to such DAGs since obs(u) is a function of the node; a tree is an instance
--   - encoding: partial observation vectors x_obs(u) → full vectors x : (i : Fin n) → dom i, with feasibility, rewards and policies required to depend only on the coordinates in obs(u); reason: Lean convention; the same problems
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - generalization: Assumption 3.1 for all nonempty families 𝒫_1, …, 𝒫_n → Assumption 3.1 only for families whose optimistic DP is measurable (MeasurableDP); reason: a weaker hypothesis; the proof applies the assumption only to the confidence sets of Algorithm 1, whose DP is measurable by the paper's assumption (p.10), and it keeps every expectation a genuine integral
--   - encoding: the paper's standing assumption that the optimistic values are measurable (p.10) → hypothesis MeasurableDP (ḡ_u and h̄_(u,v) measurable in the observations); reason: stated in the paper; it keeps every expectation in (3.4) a genuine integral
--   - encoding: n random variables X_1, …, X_n → hypothesis 1 ≤ n; reason: Λ = log(80n(T + 1)³/δ) is defined only for n ≥ 1; n = 0 is not a problem of the paper
--   - encoding: T rounds → T : ℕ with 1 ≤ T; reason: the number of rounds is a positive integer
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, proof of Theorem 3.2, (5.12), p.25

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet
import Definitions.Def_SemiBanditSOO_OptimisticDP
import Definitions.Def_SemiBanditSOO_Algorithm

open MeasureTheory

namespace SemiBanditSOO

/-- **(5.12): the gap of one stage.** Harada, Kawase, Sumita, *Beyond Monotonicity: Stochastic
Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, proof of Theorem 3.2, (5.12),
p.25.

Under Assumption 3.1, let `s̄_i = min{s_i, k_i}` with `k_i` the number of support points of `D_i`.
In a round with samples `Z_{j,1}, …, Z_{j,N_j}` of each coordinate and `D_j ∈ 𝒞_{N_j}(D̂_{j,N_j})`
for every `j` (a good round), consider an edge `(u, v)` revealing coordinate `i` with
`v ∈ 𝒜_u(x_obs(u))`, and `N_i + 1 ≤ T`. Then
`0 ≤ d ≤ 24 √(s̄_i Λ log T/(N_i + 1) · w) + 417 s̄_i Λ/(N_i + 1)`,
where `d` and `w` are the stage gap and conditional variance of the edge and
`Λ = log(80 n (T + 1)³/δ)`.

**Formalization Note.** Stated for every feasible edge revealing `i` (the paper applies it to the
edge chosen by (3.5)) and for arbitrary sample lists (the paper's are those of round `t`, with
`N_{i,t} ≤ t − 1 ≤ T − 1`). `s̄_i ∈ ℕ∞` is finite (as when `S < ∞`) and cast to `ℝ`. The optimistic
values are measurable (p.10). -/
theorem eq_5_12 {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} (Pb : Problem n dom V)
    (D : ∀ i, ProbabilityMeasure (dom i)) (s : Fin n → ℕ∞) (hs : ∀ i, 1 ≤ s i)
    (hA : Pb.Assumption31 s) (T : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hT : 1 ≤ T) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (L : ∀ j, List (dom j)) (hD : ∀ j, D j ∈ confSet (Lam n T δ) (L j))
    (hmeas : Pb.MeasurableDP (confFamily (Lam n T δ) L)) (u v : V)
    (i : Fin n) (hi : Pb.edgeCoord u v = some i) (x : Obs dom) (hfeas : v ∈ Pb.feasible u x)
    (hL : (L i).length + 1 ≤ T)
    (hfin : min (s i) (supportCount (D i : Measure (dom i))) ≠ ⊤) :
    0 ≤ Pb.stageGap D (confFamily (Lam n T δ) L) u v x ∧
    Pb.stageGap D (confFamily (Lam n T δ) L) u v x ≤
      24 * Real.sqrt (((min (s i) (supportCount (D i : Measure (dom i)))).toNat : ℝ) *
            Lam n T δ * Real.log T / ((L i).length + 1) *
            Pb.stageVar D (confFamily (Lam n T δ) L) u v x) +
        417 * ((min (s i) (supportCount (D i : Measure (dom i)))).toNat : ℝ) * Lam n T δ /
          ((L i).length + 1) := by sorry

end SemiBanditSOO
