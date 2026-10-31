-- Prove2me | Theorems.Thm_ParriloTheta_lemma_6_4
-- name    : ParriloTheta.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:11.412979+00:00
-- url     : https://prove2.me/theorems/ba573897-183f-4721-b8c6-e1b3091cdc3b
-- title:
--   Lemma 6.4 — triple sums of a $\mathcal K^{(1)}$-certificate on a union of $\alpha(G)$ cliques
-- statement:
--   Let $G=(V,E)$ be a graph with $M_G\in\mathcal K^{(1)}_n$, and let $P(1),\dots,P(n)$ be a $\mathcal K^{(1)}$-certificate for $M_G$. Let $S\subseteq V$ be such that the induced subgraph $G[S]$ is the disjoint union of $\alpha(G)$ cliques. Then for any three distinct nodes $i,j,k\in S$,
--   $$
--   P(i)_{jk}+P(j)_{ik}+P(k)_{ij}=(M_G)_{ij}+(M_G)_{jk}+(M_G)_{ik}=\alpha(G)\,|E(\{i,j,k\})|-3,
--   $$
--   where $|E(\{i,j,k\})|$ is the number of edges of $G$ among $i,j,k$.
--
--   **Formalization Note** "$G[S]$ is the disjoint union of $\alpha(G)$ cliques" is a surjective labelling $f:S\to\{0,\dots,\alpha(G)-1\}$ with distinct nodes of $S$ adjacent exactly when their labels agree. Surjectivity says that all $\alpha(G)$ cliques are nonempty, so $G[S]$ has exactly $\alpha(G)$ connected components.
--
--   Differences from the source:
--   - reading: for any {i, j, k} ⊆ S → three distinct nodes i, j, k of S; reason: {i, j, k} and |E({i, j, k})| denote a 3-element set; with repeated indices the second equality is false (i = j = k gives 3(α−1) ≠ −3)
--   - encoding: G[S] is the disjoint union of α(G) cliques → ∃ f : S → Fin α(G) surjective, ∀ u ≠ v in S, (G.Adj u v ↔ f u = f v); reason: the same condition: exactly α(G) nonempty cliques with no edge between them
--   - encoding: a graph G = (V, E) with V = [n] → G : SimpleGraph V on a finite type V; α(G) = G.indepNum; reason: Lean convention; the same graphs up to relabelling
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Lemma 6.4, p.19

import Mathlib
import Definitions.Def_ParriloTheta_InK
import Definitions.Def_ParriloTheta_graphMatrix
import Definitions.Def_ParriloTheta_IsK1Cert

namespace ParriloTheta

/-- **Lemma 6.4: triple sums on a union of `α(G)` cliques.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Lemma 6.4, p.19:
"Let G = (V, E) be a graph with MG ∈ K(1)_n and let P(1), P(2), . . . , P(n) be a K(1)-certificate
for MG. Assume that for S ⊆ V the induced subgraph G[S] is the disjoint union of α(G) cliques..
Then, for any {i, j, k} ⊆ S, we have
P(i)_jk + P(j)_ik + P(k)_ij = (MG)_ij + (MG)_jk + (MG)_ik = α(G) |E({i, j, k})| − 3."

**Formalization Note.** "G[S] is the disjoint union of α(G) cliques": there is a surjective
`f : S → Fin α(G)` such that distinct nodes of `S` are adjacent exactly when they have the same
label. Surjectivity says that all `α(G)` cliques are nonempty, i.e. `G[S]` has exactly `α(G)`
connected components, which is what the proof uses through Theorem 2.7 (p.7). `{i, j, k} ⊆ S` is
read as three distinct nodes of `S`. `|E({i, j, k})|` is the number of edges of `G` among
`i, j, k`, written as a sum of three indicators. -/
theorem lemma_6_4 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Matrix V V ℝ) (hM : InK 1 (graphMatrix G)) (hP : IsK1Cert (graphMatrix G) P)
    (S : Set V)
    (hS : ∃ f : S → Fin G.indepNum, Function.Surjective f ∧
      ∀ u v : S, u ≠ v → (G.Adj u v ↔ f u = f v))
    (i j k : V) (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    P i j k + P j i k + P k i j = graphMatrix G i j + graphMatrix G j k + graphMatrix G i k ∧
    graphMatrix G i j + graphMatrix G j k + graphMatrix G i k =
      (G.indepNum : ℝ) * ((if G.Adj i j then 1 else 0) + (if G.Adj j k then 1 else 0) +
        (if G.Adj i k then 1 else 0)) - 3 := by sorry

end ParriloTheta
