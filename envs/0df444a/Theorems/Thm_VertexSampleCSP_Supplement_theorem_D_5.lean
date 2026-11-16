-- Prove2me | Theorems.Thm_VertexSampleCSP_Supplement_theorem_D_5
-- name    : VertexSampleCSP.Supplement.theorem_D_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:59:42.785121+00:00
-- url     : https://prove2.me/theorems/b859196a-0624-45e3-ae7b-0419513d3e28
-- title:
--   Theorem D.5 — vertex percolation for Max-Cut: $\mathbb E|p^{-2}\mathrm{mc}(G_p)-\mathrm{mc}(G)|\le17\sqrt2R(G)/\sqrt p$ and $\mathbb E|\kappa(G_p)-\kappa(G)|\le36\sqrt{n/(pm)}$
-- statement:
--   Let $G$ be a graph with $n$ vertices and $m>0$ edges, let $d_v$ be the degree of $v$ and $R(G)=\sum_v\sqrt{d_v}$. For $0<p\le1$ let $G_p$ be the subgraph of $G$ induced by a random vertex set containing every vertex independently with probability $p$. Write $\mathrm{mc}$ for the maximum cut and $\kappa=\mathrm{mc}/(\text{number of edges})$ for the max-cut density, with $\kappa=0$ for edgeless graphs. Then:
--
--   1. for every $0<p\le 1$,
--   $$\mathbb E\,\big|p^{-2}\mathrm{mc}(G_p)-\mathrm{mc}(G)\big|\le 17\sqrt2\,\frac{R(G)}{\sqrt p}\le 34\sqrt{\frac{nm}{p}};$$
--   2. for every $0<p\le 1$,
--   $$\mathbb E\,\big|\kappa(G_p)-\kappa(G)\big|\le 36\sqrt{\frac{n}{pm}};$$
--   3. for $p=\tfrac12$,
--   $$\mathbb E\,\big|\kappa(G_{1/2})-\kappa(G)\big|\le 7\sqrt2\sqrt{n/m}<10\sqrt{n/m}.$$
--
--   This is the formal version of Theorem 1.3; it gives the answer to Zhao's question (Corollary 1.4): the half-sample preserves the max-cut density whenever $m/n\to\infty$, at every density and without degree assumptions.
--
--   **Formalization Note** The expectation over $G_p$ is the published finite Bernoulli average `bernAvg`. $n$ counts all vertices, isolated ones included.
--
--   Differences from the source:
--
--   - encoding: G_p, the subgraph induced by keeping every vertex independently with probability p, and E over it → bernAvg p over S : Finset V of the quantity for G[S] (maxCutOn G S, kappaOn G S); reason: bernAvg is the exact finite expectation over the Bernoulli(p) vertex set; G[S] is represented by its edges inside S
--   - encoding: κ = 0 for edgeless graphs → kappaOn G S = maxCutOn G S / edgesOn G S in ℝ, which is 0 / 0 = 0 when G[S] has no edge; reason: same value on every graph
--   - encoding: the bound for p = 1/2 stated after the clause for 0 < p ≤ 1 → a separate conjunct at p = 1/2 alongside the ∀ p clause; reason: the p = 1/2 bound is an additional conclusion, not a hypothesis of the theorem
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem D.5 (Theorem 1.3), p.20 (PDF p.22); informal form Theorem 1.3, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_VertexSampleCSP_bernAvg
import Definitions.Def_VertexSampleCSP_Supplement_maxCutOn

namespace VertexSampleCSP.Supplement

/-- **Theorem D.5 (Theorem 1.3, vertex percolation for Max-Cut).** Chang, *Optimal Vertex Sampling
for Constraint Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…),
Theorem D.5, p.20 (PDF p.22): "For every graph G with n vertices and m > 0 edges and every
0 < p ≤ 1, E |p^{−2}mc(G_p) − mc(G)| ≤ 17√2 R(G)/√p ≤ 34√(nm/p), E |κ(G_p) − κ(G)| ≤ 36√(n/(pm)),
and for p = 1/2 the last bound improves to 7√2√(n/m) < 10√(n/m)."

`G_p` is the subgraph of `G` induced on a random vertex set `S` containing every vertex
independently with probability `p`; the expectation over it is the published `bernAvg p`.

**Formalization Note.** `n = |V|` counts every vertex, isolated ones included; `m` is the number of
edges of `G`. `mc(G_p) = maxCutOn G S`, `mc(G) = maxCutOn G univ`, `κ(G_p) = kappaOn G S` (with
`κ = 0` for an edgeless `G_p`, through `0 / 0 = 0`), `κ(G) = kappaOn G univ`, and
`R(G) = degSqrtSum G = Σ_v √d_v`. The two inequalities of the chain and the strict inequality of the
last clause are all part of the conclusion. -/
theorem theorem_D_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hm : 0 < G.edgeFinset.card) :
    (∀ p : ℝ, 0 < p → p ≤ 1 →
      bernAvg p (fun S => |(p ^ 2)⁻¹ * (maxCutOn G S : ℝ) - (maxCutOn G Finset.univ : ℝ)|)
          ≤ 17 * Real.sqrt 2 * degSqrtSum G / Real.sqrt p ∧
        17 * Real.sqrt 2 * degSqrtSum G / Real.sqrt p
          ≤ 34 * Real.sqrt ((Fintype.card V : ℝ) * (G.edgeFinset.card : ℝ) / p) ∧
        bernAvg p (fun S => |kappaOn G S - kappaOn G Finset.univ|)
          ≤ 36 * Real.sqrt ((Fintype.card V : ℝ) / (p * (G.edgeFinset.card : ℝ)))) ∧
    bernAvg (1 / 2 : ℝ) (fun S => |kappaOn G S - kappaOn G Finset.univ|)
        ≤ 7 * Real.sqrt 2 * Real.sqrt ((Fintype.card V : ℝ) / (G.edgeFinset.card : ℝ)) ∧
      7 * Real.sqrt 2 * Real.sqrt ((Fintype.card V : ℝ) / (G.edgeFinset.card : ℝ))
        < 10 * Real.sqrt ((Fintype.card V : ℝ) / (G.edgeFinset.card : ℝ)) := by sorry

end VertexSampleCSP.Supplement
