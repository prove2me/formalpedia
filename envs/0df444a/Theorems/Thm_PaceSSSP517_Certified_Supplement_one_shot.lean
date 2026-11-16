-- Prove2me | Theorems.Thm_PaceSSSP517_Certified_Supplement_one_shot
-- name    : PaceSSSP517.Certified.Supplement.one_shot
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:33:47.820206+00:00
-- url     : https://prove2.me/theorems/3fb47403-1377-4d10-b760-52f308307dd8
-- title:
--   Theorem 3.7 — One-shot learning in the bulk regime
-- statement:
--   Let $G,H,s_0,n,k,\varepsilon$ satisfy the published PACE model: a connected simple undirected positive-real weighted graph, a $(2k-1+\varepsilon)$-spanner, $k\ge2$, $0<\varepsilon<1$, $k\le\ln n$, and $12k^2\le\varepsilon n$. Use PACE's budget $s=(20/\varepsilon)kn^{1+1/k}\ln n$. Consider any supported executed prefix, and suppose all rounds $r_0,\ldots,r_1-1$ are bulk. Only profiles present in the prefix are used below.
--
--   1. Every edge fails in at most one of those rounds. An edge failing in the interval fails in no later executed round, even outside the interval.
--   2. For every such round whose successor is executed, $d_{r+1}\le\operatorname{BF}_G(d_r)$ pointwise, over all edges in both orientations.
--   3. For every oriented edge $(u,v)$ with $d_{r+1}(v)>d_{r+1}(u)+w(u,v)$,
--   $$
--   J(e;d_{r+1})\le\frac{d_r(u)-d_{r+1}(u)}{w(e)}.
--   $$
--   4. For every $L\ge1$ with $r_0+L\le r_1$, put $S_L=\{r_0,\ldots,r_0+L-1\}$ and $J_L^\star=\max_{j\in S_L,e\in E}J(e;d_j)$. Then
--   $$
--   \kappa_{S_L}\le J_L^\star/L,\qquad J_L^\star\le2k-1.
--   $$
--   The least qualifying positive length $L^\star$ exists, satisfies $L^\star\ge J_{L^\star}^\star/\varepsilon$, is minimal among qualifying lengths, and obeys $L^\star\le\lceil(2k-1)/\varepsilon\rceil$. If $r_0+L^\star\le r_1$, PACE stops by $r_0+L^\star-1$; its actual final tree realizes a profile at most $(1+\varepsilon)\operatorname{dist}_G(s_0,\cdot)$.
--   5. For every $t\ge0$ with $r_0+t\le r_1$ and that profile executed,
--   $$
--   d_{r_0+t}\le\operatorname{BF}_G^t(d_{r_0}).
--   $$
--   If $r_0+h(G)\le r_1$ and that round is executed, its profile is the full-graph distance, its violating weight is zero, its tree is exact and its stop flag is set. It stops by $\min\{r_1,r_0+h(G)\}$ in this case.
--
--   This deterministic companion theorem uses the published Lemmas 3.1 and 3.2 (ids a30c6d5b-1d2e-4b3d-92a6-cfd0d670b856 and 880eb6c6-4242-4c6f-9c2f-9d625c96b69d); it is not used in the proof of the inherited goal.
--
--   Differences from the source:
--   - encoding: finite connected positive-real weighted undirected graph and finite profiles → published graph and Algorithm 1 modules with Fin n vertices and one stored orientation per edge; reason: canonical storage permits walks and the Bellman–Ford operator to use both orientations; connected spanners make every asserted real distance finite
--   - generalization: H computed by the upstream spanner routine → any H satisfying the same (2k−1+ε) all-pairs spanner condition; reason: the added results have no space clause and use only this condition; the prescribed routine output is an instance
--   - encoding: deterministically on the actual PACE execution → every SampleTrace whose trajectory equals its executed prefix, using one-based executed indices; reason: SampleTrace is the support restriction of the conditional Bernoulli choices including probability-one and probability-zero edges; unsupported samples are excluded
--   - encoding: bulk interval r0,…,r1−1 and its successor profiles → r1 may be one past the finite prefix; successor and iterate claims require the mentioned profile to exist; reason: finite prefixes have no next profile; every existing profile and completely observed bulk window remains covered
--   - encoding: least positive L satisfying L ≥ J_L⋆/ε → least qualifying length using zero extension of jump records outside the finite execution; reason: this totalizes the search after termination; it preserves executed windows, their least qualifying length when present, and the source stopping proviso
--   - reading: an exact tree is certified by min{r1,r0+h(G)} → if r0+h(G) lies within the bulk interval endpoint and is executed, that profile and tree are exact, W is zero and the stop flag fires by that round; reason: A.6(v) proves exactness after h(G) bulk relaxations if the run has not stopped earlier; it does not establish exactness at r1 when fewer bulk relaxations exist
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 7-8, Theorem 3.7; proof A.6, pp. 18–19

import Definitions.Def_PaceSSSP517_Certified_Supplement_GraphOperators
import Definitions.Def_PaceSSSP517_Certified_Supplement_TraceStatistics

set_option autoImplicit false
open scoped ENNReal NNReal

namespace PaceSSSP517.Certified.Supplement

/-- Theorem 3.7, pp.7–8; proof A.6, pp.18–19. All five parts.
Only existing executed profiles are mentioned. The right endpoint may be one
past the prefix; successor/exactness claims require that endpoint to be present.
The exactness reading is the conditional one explicitly proved in A.6(v).
The zero extension in windowJump totalizes the least-window search only. -/
theorem one_shot
    (n k : ℕ) (ε : ℝ) (G : WeightedGraph n) (H : Finset (Edge n)) (s₀ : Fin n)
    (hparams : Parameters n k ε) (hG : Connected G.edges)
    (hH : IsSpanner G H (2 * (k : ℝ) - 1 + ε))
    (Fs : List (Finset (Edge n))) (hFs : SampleTrace G H s₀ k ε Fs)
    (hexecuted : execution (trajectory G H s₀ k ε Fs).rounds =
      (trajectory G H s₀ k ε Fs).rounds)
    (r₀ r₁ : ℕ) (hstart : 1 ≤ r₀) (horder : r₀ ≤ r₁)
    (hend : r₁ ≤ Fs.length + 1)
    (hbulk : ∀ j ∈ Finset.Ico r₀ r₁,
      (roundAt (trajectory G H s₀ k ε Fs).rounds j).bulk = true) :
    let ts := (trajectory G H s₀ k ε Fs).rounds
    -- (i) One failure in the bulk window, and no later re-failure anywhere.
    (∀ e ∈ G.edges,
      (failureRounds G ts (Finset.Ico r₀ r₁) e).card ≤ 1 ∧
      ∀ r ∈ Finset.Ico r₀ r₁, fails G (profile ts r) e →
        ∀ r' ∈ past ts.length, r < r' → ¬ fails G (profile ts r') e) ∧
    -- (ii) Whole-graph Bellman–Ford domination, both edge orientations.
    (∀ r ∈ Finset.Ico r₀ r₁, r + 1 ≤ ts.length →
      ∀ v, profile ts (r + 1) v ≤ BF G (profile ts r) v) ∧
    -- (iii) Jump versus the improvement of its lower endpoint.
    (∀ r ∈ Finset.Ico r₀ r₁, r + 1 ≤ ts.length →
      ∀ u v : Fin n, edge u v ∈ G.edges →
        profile ts (r + 1) u + G.weight (edge u v) < profile ts (r + 1) v →
        jump G (profile ts (r + 1)) (edge u v) ≤
          (profile ts r u - profile ts (r + 1) u) / G.weight (edge u v)) ∧
    -- (iv) Every window, the least qualifying length, its bound, and stopping.
    (∀ L : ℕ, 1 ≤ L → r₀ + L ≤ r₁ →
      kappa G ts (window r₀ L) ≤ windowJump G ts r₀ L / (L : ℝ) ∧
      windowJump G ts r₀ L ≤ 2 * (k : ℝ) - 1) ∧
    (let Lstar := firstWindow G ts ε r₀;
      1 ≤ Lstar ∧ windowJump G ts r₀ Lstar / ε ≤ (Lstar : ℝ) ∧
      (∀ L : ℕ, 1 ≤ L → windowJump G ts r₀ L / ε ≤ (L : ℝ) → Lstar ≤ L) ∧
      Lstar ≤ ⌈(2 * (k : ℝ) - 1) / ε⌉₊ ∧
      (r₀ + Lstar ≤ r₁ →
        stopped ts ∧ ts.length ≤ r₀ + Lstar - 1 ∧
        ∃ t, ts.getLast? = some t ∧ t.stopping = true ∧
          t.tree ⊆ G.edges ∧ Connected t.tree ∧ t.tree.card + 1 = n ∧
          ∀ v, t.d v ≤ (1 + ε) * distance G G.edges s₀ v ∧
            edistance G t.tree s₀ v = ENNReal.ofReal (t.d v))) ∧
    -- (v) All iterates, and the exactness stop when its round is reached.
    (∀ t : ℕ, r₀ + t ≤ r₁ → r₀ + t ≤ ts.length →
      ∀ v, profile ts (r₀ + t) v ≤ ((BF G)^[t]) (profile ts r₀) v) ∧
    (r₀ + hopDiameter G s₀ ≤ r₁ → r₀ + hopDiameter G s₀ ≤ ts.length →
      (∀ v, profile ts (r₀ + hopDiameter G s₀) v = distance G G.edges s₀ v) ∧
      (∑ e ∈ violators G (profile ts (r₀ + hopDiameter G s₀)),
        qat G ts (r₀ + hopDiameter G s₀) e) = 0 ∧
      (roundAt ts (r₀ + hopDiameter G s₀)).stopping = true ∧
      IsShortestTree G G.edges s₀ (roundAt ts (r₀ + hopDiameter G s₀)).tree ∧
      stopped ts ∧ ts.length ≤ min r₁ (r₀ + hopDiameter G s₀)) := by sorry

end PaceSSSP517.Certified.Supplement
