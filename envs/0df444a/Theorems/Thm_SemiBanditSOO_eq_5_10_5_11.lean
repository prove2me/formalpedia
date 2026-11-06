-- Prove2me | Theorems.Thm_SemiBanditSOO_eq_5_10_5_11
-- name    : SemiBanditSOO.eq_5_10_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:00:11.468201+00:00
-- url     : https://prove2.me/theorems/c223b3d5-44d9-4bf5-b901-e7685bd86908
-- title:
--   (5.10)–(5.11) — in one good round, $\mathbb E[\sum_hw_{t,h}]\le1$ and $\mathrm{Reg}_t\le\mathbb E[\sum_hd_{t,h}]$
-- statement:
--   Let $\mathcal P_1,\dots,\mathcal P_n$ be sets of distributions with $D_i\in\mathcal P_i$, and let $\sigma$ be the policy that chooses by (3.5) for the optimistic DP of these sets. Run $\sigma$ on $X\sim D$, and let $d_h$ and $w_h$ be the gap and the conditional variance of the stage $h$ of the path: when the edge $(u_h,u_{h+1})=(u,v)$ reveals $i$,
--   $$d_h=\sup_{Q\in\mathcal P_i}\mathbb E_{X_i\sim Q}[\bar g_v(X_i,x_{\mathrm{obs}(u)})]-\mathbb E_{X_i\sim D_i}[\bar g_v(X_i,x_{\mathrm{obs}(u)})],\qquad w_h=\mathrm{Var}_{X_i\sim D_i}\bigl(\bar g_v(X_i,x_{\mathrm{obs}(u)})\bigr),$$
--   and $d_h=w_h=0$ at a stopping edge and after the leaf. Then
--   $$\mathbb E\Bigl[\sum_hw_h\Bigr]\le1\quad(5.10),\qquad \mathrm{OPT}(D)-f(\sigma\mid D)\le\mathbb E\Bigl[\sum_hd_h\Bigr]\quad(5.11).$$
--
--   These bound the regret of one good round by its cumulative gap, and its total variance by $1$.
--
--   **Formalization Note.** $d_h$ and $w_h$ are the paper's explicit expressions for $Y_h-\mathbb E[Y_{h+1}\mid\mathcal F_h]$ and $\mathrm{Var}(Y_{h+1}\mid\mathcal F_h)$ (p.25), summed along the path; the expectation is over $X\sim D$. The optimistic DP is assumed measurable, as in the paper.
--
--   Differences from the source:
--   - generalization: the confidence sets 𝒞_{i,t} of a good round (D_i ∈ 𝒞_{i,t}) → any family of sets of distributions 𝒫_i with D_i ∈ 𝒫_i; reason: the argument uses only D_i ∈ 𝒫_i; the confidence sets of a good round are an instance
--   - encoding: d_{t,h} = Y_{t,h} − 𝔼[Y_{t,h+1} | 𝓕_{t,h}] and w_{t,h} = Var(Y_{t,h+1} | 𝓕_{t,h}) → the paper's explicit expressions for them (p.25), summed along the path of σ on X; reason: the paper identifies the two (the unobserved coordinate still follows D_i given 𝓕_{t,h})
--   - generalization: a finite rooted decision tree → a finite rooted DAG (every node reachable from the root, a height function strictly decreasing along edges); reason: footnote 1 (p.6) states that the analysis applies to such DAGs since obs(u) is a function of the node; a tree is an instance
--   - encoding: partial observation vectors x_obs(u) → full vectors x : (i : Fin n) → dom i, with feasibility, rewards and policies required to depend only on the coordinates in obs(u); reason: Lean convention; the same problems
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - encoding: OPT(D) = sup over (possibly randomized) policies → sup over measurable deterministic policies; reason: a randomized policy is a distribution over deterministic ones, so its value is an average of deterministic values and the supremum is the same
--   - encoding: ties in (3.5) broken in a fixed order → least maximizer for an arbitrary linear order on the node type (the statement holds for every order); reason: a fixed order is a linear order on the nodes
--   - encoding: the paper's standing assumption that the optimistic values are measurable (p.10) → hypothesis MeasurableDP (ḡ_u and h̄_(u,v) measurable in the observations); reason: stated in the paper; it keeps every expectation in (3.4) a genuine integral
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, proof of Theorem 3.2, (5.10)–(5.11), pp.24–25

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_OptimisticDP

open MeasureTheory

namespace SemiBanditSOO

/-- **(5.10)–(5.11): one good round.** Harada, Kawase, Sumita, *Beyond Monotonicity: Stochastic
Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, proof of Theorem 3.2,
(5.10)–(5.11), pp.24–25.

Run the policy `σ` that chooses by (3.5) for families `𝒫_i ∋ D_i` on `X ∼ D`, visiting
`u_0 = r, u_1, …`. With `d_h` and `w_h` the gap and the conditional variance of stage `h`
(`d_h = sup_{Q∈𝒫_i} 𝔼_Q[ḡ_v(X_i, x_obs(u))] − 𝔼_{D_i}[ḡ_v(X_i, x_obs(u))]` and
`w_h = Var_{D_i}(ḡ_v(X_i, x_obs(u)))` when the edge `(u_h, u_{h+1}) = (u, v)` reveals `i`, and `0`
otherwise),
`𝔼[Σ_h w_h] ≤ 1` (5.10) and `OPT(D) − f(σ | D) ≤ 𝔼[Σ_h d_h]` (5.11).

**Formalization Note.** `d_h` and `w_h` are the paper's explicit expressions (p.25) for
`Y_h − 𝔼[Y_{h+1} | ℱ_h]` and `Var(Y_{h+1} | ℱ_h)`, summed along the path of `σ` on `X` (stages after
the leaf contribute `0`). The paper states this for the confidence sets of a good round; it is
stated for every family containing the `D_i` whose optimistic values are measurable (p.10). -/
theorem eq_5_10_5_11 {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} [Fintype V] [LinearOrder V]
    (Pb : Problem n dom V) (D : ∀ i, ProbabilityMeasure (dom i))
    (P : ∀ i, Set (ProbabilityMeasure (dom i))) (hD : ∀ i, D i ∈ P i)
    (hmeas : Pb.MeasurableDP P) :
    ∫ x, Pb.pathSum (Pb.greedy P) (Pb.stageVar D P) x ∂(prodDist D) ≤ 1 ∧
    Pb.OPT D - Pb.value D (Pb.greedy P) ≤
      ∫ x, Pb.pathSum (Pb.greedy P) (Pb.stageGap D P) x ∂(prodDist D) := by sorry

end SemiBanditSOO
