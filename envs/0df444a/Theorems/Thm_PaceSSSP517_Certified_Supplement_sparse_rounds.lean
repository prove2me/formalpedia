-- Prove2me | Theorems.Thm_PaceSSSP517_Certified_Supplement_sparse_rounds
-- name    : PaceSSSP517.Certified.Supplement.sparse_rounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:34:38.376977+00:00
-- url     : https://prove2.me/theorems/e5a4287e-9428-4c94-998e-27eab2eda950
-- title:
--   Theorem 3.10 — Few reweighting rounds (corrected: at least one round when J⋆=0)
-- statement:
--   Use the same graph, source, spanner and standing PACE parameters as Theorem 3.7. Let $m=|E|$, $s=(20/\varepsilon)kn^{1+1/k}\ln n$, $\gamma=m/s$, and
--   $$
--   R_{\rm wc}=\lceil11k^2/\varepsilon\rceil,\qquad
--   T=\left\lfloor\min\{5k/\varepsilon,\;kn^{2/k}/(3\varepsilon\gamma)\}\right\rfloor.
--   $$
--   For the actual execution stopped at its first certificate, let $J^\star$ be the largest relative jump in any executed round, $C=\max\{1,\lceil J^\star/\varepsilon\rceil\}$, $B=\lceil12k\gamma\rceil$, and $B_{\rm early}=\lceil4\gamma\rceil$. Under the adaptive sampling law through horizon $R_{\rm wc}$, all the following hold jointly with probability at least
--   $$
--   1-R_{\rm wc}n^{-n}-R_{\rm wc}\exp(-s/3).
--   $$
--
--   1. $J^\star\le2k-1$. The number $N$ of executed non-bulk rounds satisfies $N<12k\gamma$ strictly. If the execution reaches round $B$, a round in $1,\ldots,B$ is bulk. The bulk rounds form at most $B$ maximal consecutive intervals.
--   2. Among executed rounds $j\le T$, fewer than $4\gamma$ are non-bulk.
--   3. PACE stops at a positive round $R$ satisfying
--   $$
--   R\le\min\{R_{\rm wc},BC\},\qquad
--   B_{\rm early}C\le T\ \Longrightarrow\ R\le B_{\rm early}C.
--   $$
--   Its final tree is a connected spanning tree in $G$, realizes the final profile, and that profile is at most $(1+\varepsilon)\operatorname{dist}_G(s_0,\cdot)$ at every vertex.
--
--   The correction is necessary for a unit-weight path on 1000 vertices, $k=2$, $\varepsilon=1/2$: every connected spanning subgraph is the full path, so PACE stops exactly at round 1, whereas the printed bound is zero. The companion theorem uses base Lemmas 3.1, 3.2, 3.4 and 3.5 (ids recorded in MODERATION_NOTES.md) and Theorem 3.7's window conclusion. It has no resource clause.
--
--   Differences from the source:
--   - encoding: finite connected positive-real weighted undirected graph and finite profiles → published graph and Algorithm 1 modules with Fin n vertices and one stored orientation per edge; reason: canonical storage permits walks and the Bellman–Ford operator to use both orientations; connected spanners make every asserted real distance finite
--   - generalization: H computed by the upstream spanner routine → any H satisfying the same (2k−1+ε) all-pairs spanner condition; reason: the added results have no space clause and use only this condition; the prescribed routine output is an instance
--   - encoding: probability on the event of Theorem 3.6 → one joint event under the published runLaw through Rwc with the full printed lower probability bound; reason: the product-kernel law implements conditional independent sampling and the absorbing actual execution; no per-clause or conditional probability replaces the joint bound
--   - reading: the first bulk round is at most ceil(12kγ) → if the execution reaches ceil(12kγ), a bulk round exists among rounds 1 through that bound; reason: an execution may terminate at a non-bulk round before any bulk round; the source counting argument gives this implication
--   - correction: both stopping products use ceil(J⋆/ε) → both products use max{1,ceil(J⋆/ε)}; reason: a unit-weight path on n=1000 vertices with k=2 and ε=1/2 satisfies every standing assumption, H=G, stops at round 1 and has J⋆=0, while the printed bound is zero; the correction changes no positive-jump instance
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 8, Theorem 3.10; proof A.8, pp. 19–20

import Definitions.Def_PaceSSSP517_Certified_Supplement_TraceStatistics

set_option autoImplicit false
open scoped ENNReal NNReal

namespace PaceSSSP517.Certified.Supplement

/-- Theorem 3.10, p.8, proof A.8 pp.19–20. Corrected only at J⋆=0:
max 1 ⌈J⋆/ε⌉ replaces ⌈J⋆/ε⌉, since an already exact run stops at round 1.
The graph, parameters and source satisfy precisely the base standing assumptions.
Any spanner with the prescribed stretch is allowed; no space interface is needed. -/
theorem sparse_rounds
    (n k : ℕ) (ε : ℝ) (G : WeightedGraph n) (H : Finset (Edge n)) (s₀ : Fin n)
    (hparams : Parameters n k ε) (hG : Connected G.edges)
    (hH : IsSpanner G H (2 * (k : ℝ) - 1 + ε)) :
    let Rwc := roundCap k ε
    let γ := density G k ε
    let T := earlyHorizon G k ε
    ENNReal.ofReal (1 - (Rwc : ℝ) * ((n : ℝ)^n)⁻¹ -
      (Rwc : ℝ) * Real.exp (-budget n k ε / 3)) ≤
    probability (runLaw G H s₀ k ε Rwc)
      {ts |
        let Jstar := executionJump G ts
        let C := max 1 ⌈Jstar / ε⌉₊
        let B := ⌈12 * (k : ℝ) * γ⌉₊
        let Bearly := ⌈4 * γ⌉₊
        Jstar ≤ 2 * (k : ℝ) - 1 ∧
        -- (i) Strict total count, first-bulk bound when that round is reached,
        -- and number of maximal bulk intervals.
        ((nonBulkRounds ts ts.length).card : ℝ) < 12 * (k : ℝ) * γ ∧
        (B ≤ ts.length → ∃ r ∈ Finset.Icc 1 B, (roundAt ts r).bulk = true) ∧
        bulkRunCount ts ≤ B ∧
        -- (ii) Strict early-round count, including the possible T=0 case.
        ((nonBulkRounds ts T).card : ℝ) < 4 * γ ∧
        -- (iii) Both corrected stopping bounds and the actual output tree.
        1 ≤ ts.length ∧ stopped ts ∧ ts.length ≤ min Rwc (B * C) ∧
        (Bearly * C ≤ T → ts.length ≤ Bearly * C) ∧
        ∃ t, ts.getLast? = some t ∧ t.stopping = true ∧
          t.tree ⊆ G.edges ∧ Connected t.tree ∧ t.tree.card + 1 = n ∧
          ∀ v, t.d v ≤ (1 + ε) * distance G G.edges s₀ v ∧
            edistance G t.tree s₀ v = ENNReal.ofReal (t.d v)} := by sorry

end PaceSSSP517.Certified.Supplement
