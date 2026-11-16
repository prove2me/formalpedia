-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_theorem_5
-- name    : RamseyDisambig.Spherical.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:27:22.91917+00:00
-- url     : https://prove2.me/theorems/b61f747e-70e2-456a-9899-cb99f6cfaaa2
-- title:
--   Theorem 5 — A partial graph of VC-dimension ≤ 1 with homogeneous pure triples and universal disambiguations
-- statement:
--   For every $k\in\mathbb N$ there is a finite partial graph $G$ such that
--
--   1. $G$ has VC-dimension at most $1$, the VC-dimension being that of its adjacency matrix with $\star$ on the diagonal;
--   2. every pure induced subgraph of $G$ on three vertices is homogeneous, that is, a triangle or an independent set;
--   3. every disambiguation $G'$ of $G$ contains every $k$-vertex graph as an induced subgraph:
--   $$\forall F\text{ on }k\text{ vertices}:\quad F\hookrightarrow_{\mathrm{ind}} G'.$$
--
--   This is the symmetric analogue of Theorem 3 for partial graphs; without the VC-dimension requirement the conclusion follows from the Nešetřil–Rödl theorem.
--
--   **Formalization Note** $G$ is a partial graph on `Fin n`; disambiguations are simple graphs on `Fin n` containing every edge and no non-edge of $G$. All three conclusions are stated in one conjunction.
--
--   Differences from the source:
--   - generalization: k ∈ ℕ, read as a positive integer → every k : ℕ, including k = 0; reason: the case k = 0 is automatic since VC-dimension and induced containment of the 0-vertex graph are trivial; it specializes to the source's k ≥ 1
--   - encoding: a finite partial graph and its VC-dimension → PartialGraph (Fin n): a symmetric Option Bool adjacency with none on the diagonal; VC-dimension = partialVCDim of that adjacency matrix; reason: the adjacency matrix with ⋆ on the diagonal, as on pp. 5, 19
--   - encoding: pure induced subgraph on three vertices is homogeneous → for pairwise distinct u, v, w with all three pairs specified, the three values agree; reason: complete or edgeless means all three pairs are edges or all are non-edges
--   - encoding: every disambiguation contains every k-vertex graph as an induced subgraph → every SimpleGraph G' on Fin n preserving 1-edges and 0-edges admits an induced embedding of every SimpleGraph (Fin k); reason: disambiguations as on p. 19; ↪g is induced
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Theorem 5, p. 5 (restated p. 19, proof pp. 19–20) (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_PartialGraph

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Theorem 5, p. 5 (restated p. 19, proof pp. 19–20): all three conclusions. -/
theorem theorem_5 (k : ℕ) :
    ∃ (n : ℕ) (G : PartialGraph (Fin n)),
      graphVCDim G ≤ 1 ∧ PureTriplesHomogeneous G ∧
      ∀ G' : SimpleGraph (Fin n),
        IsGraphDisambiguation G G' → ContainsAllInduced G' k := by sorry

end RamseyDisambig.Spherical.Supplement
