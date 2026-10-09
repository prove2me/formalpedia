-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_clique_plus_pendants
-- name    : TaitTobin.Irregularity.clique_plus_pendants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:37.64575+00:00
-- url     : https://prove2.me/theorems/7c336696-ea88-4f37-ae5f-74366daceb82
-- title:
--   Proof of Theorem 21, pp. 20–21 — W = ∅: a maximizer is a clique together with pendant vertices
-- statement:
--   There is $N$ such that for every $n \ge N$, every connected graph $G$ on $n$ vertices maximizing $\lambda_1 - d$ consists of a clique together with pendant vertices: there is a set $U$ of vertices such that
--
--   1. any two distinct vertices of $U$ are adjacent, and
--   2. every vertex $z \notin U$ has degree $1$, and its neighbour lies in $U$.
--
--   This is the state of the proof of Theorem 21 after the set $W$ of Proposition 20 has been shown to be empty; what remains is to show that all pendant vertices hang from the same clique vertex.
--
--   **Formalization Note** No eigenvector appears: the statement is purely combinatorial. It does not assert that the pendant vertices share their neighbour, which is the last step of Theorem 21.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, pp. 20–21, proof of Theorem 21 ("We begin by showing that the set W must be empty", p. 20; "At this point we know that G consists of a clique together with a set of pendant vertices V", p. 21)

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Proof of Theorem 21, pp. 20–21: for `n` large, a maximizer `G` of `λ₁ − d` consists of a clique
`U` together with pendant vertices: every vertex outside `U` has degree one and its neighbour lies
in `U`. -/
theorem clique_plus_pendants : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsIrregMax G →
    ∃ U : Finset (Fin n), (∀ a ∈ U, ∀ b ∈ U, a ≠ b → G.Adj a b) ∧
      ∀ z : Fin n, z ∉ U → G.degree z = 1 ∧ ∃ u ∈ U, G.Adj z u := by sorry
end TaitTobin.Irregularity
