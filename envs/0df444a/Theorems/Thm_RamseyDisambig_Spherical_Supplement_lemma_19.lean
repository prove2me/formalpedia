-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_lemma_19
-- name    : RamseyDisambig.Spherical.Supplement.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:26:53.043536+00:00
-- url     : https://prove2.me/theorems/f63f41e5-e33c-4418-903e-96bb90c0e17d
-- title:
--   Lemma 19 — A tame partial graph with two universal uniform fillings
-- statement:
--   For every $k\in\mathbb N$ there is a finite partial graph $U$ such that
--
--   1. no vertex of $U$ is incident to both an edge and a non-edge;
--   2. the graph $U^{(1)}$ obtained by casting every $\star$ of $U$ into an edge, and the graph $U^{(0)}$ obtained by casting every $\star$ into a non-edge, both contain every $k$-vertex graph as an induced subgraph:
--   $$\forall F \text{ on } k \text{ vertices}:\quad F\hookrightarrow_{\mathrm{ind}} U^{(1)}\quad\text{and}\quad F\hookrightarrow_{\mathrm{ind}} U^{(0)}.$$
--
--   This partial graph is the building block that Theorem 5 amplifies with the girth Ramsey theorem.
--
--   **Formalization Note** $U$ is a partial graph on `Fin n`; induced containment is an induced embedding `F ↪g G'` of every simple graph on `Fin k`.
--
--   Differences from the source:
--   - reading: there exists a partial graph U (finiteness not stated) → a finite U on Fin n; reason: the stronger reading: the proof's U is finite and Theorem 5 applies the girth Ramsey theorem to a finite graph built from it
--   - generalization: k ∈ ℕ, read as a positive integer → every k : ℕ, including k = 0; reason: the case k = 0 is automatic since VC-dimension and induced containment of the 0-vertex graph are trivial; it specializes to the source's k ≥ 1
--   - encoding: partial graph, casting ⋆s, containing all k-vertex graphs as induced subgraphs → symmetric Option Bool adjacency, none on the diagonal; castToEdges / castToNonEdges; an induced embedding of every SimpleGraph (Fin k); reason: the same partial graphs and the same induced containment
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 19, p. 19 (proof p. 19) (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_PartialGraph

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Lemma 19, p. 19. The witness is a finite partial graph; both uniform fillings are required. -/
theorem lemma_19 (k : ℕ) :
    ∃ (n : ℕ) (U : PartialGraph (Fin n)),
      NoVertexMixed U ∧ ContainsAllInduced (castToEdges U) k ∧
      ContainsAllInduced (castToNonEdges U) k := by sorry

end RamseyDisambig.Spherical.Supplement
