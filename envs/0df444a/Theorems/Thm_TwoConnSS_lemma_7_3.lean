-- Prove2me | Theorems.Thm_TwoConnSS_lemma_7_3
-- name    : TwoConnSS.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:44:52.826086+00:00
-- url     : https://prove2.me/theorems/a23bde18-5bc6-4c48-b820-494bbadfe436
-- title:
--   Lemma 7.3 — the 3-matching lemma
-- statement:
--   Let $G$ be a finite simple 2-vertex-connected graph with no non-trivial 2-vertex cut. Then for every partition $V(G) = X \,\dot\cup\, Y$ with $|X|, |Y| \ge 4$, the cut $E_G(X, Y)$ contains a matching of size three.
--
--   The lemma turns the separator exclusions of preprocessing into the 3-matching property, which supplies three disjoint connections across any balanced cut in all exchange arguments.
--
--   Differences from the source:
--   - encoding: a matching of size three in E_G(X, Y) → three edges a_i b_i with a_i ∈ X, b_i ∉ X, the a_i pairwise distinct and the b_i pairwise distinct; reason: this is what a matching of three cut edges is
--   - encoding: a 2VC graph (p.23: all input graphs are finite) → a simple graph on an arbitrary finite vertex type; reason: same objects; Fin n is an instance
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Lemma 7.3, p.27 (PDF p.28)

import Mathlib
import Definitions.Def_TwoConnSS_HasThreeMatching

namespace TwoConnSS

/-- **Lemma 7.3 (3-matching lemma).**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Lemma 7.3, p.27: "A 2VC graph with
no non-trivial 2-vertex cut has the 3-matching property."

Let `G` be a finite simple graph with at least three vertices such that deleting any vertex leaves
it connected, and with no non-trivial 2-vertex cut. Then for every partition `V = X ∪̇ Y` with
`|X|, |Y| ≥ 4`, some three edges of `G` between `X` and `Y` have pairwise distinct ends.

**Formalization Note.** Stated for an arbitrary finite vertex type. -/
theorem lemma_7_3 {V : Type*} [Fintype V] (G : SimpleGraph V) (h2 : IsTwoVC G)
    (hcut : ∀ u v, ¬ IsNontrivialTwoCut G u v) : HasThreeMatching G := by sorry

end TwoConnSS
