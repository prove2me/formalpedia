-- Prove2me | Theorems.Thm_TaitTobin_Outerplanar_outerplanar_facts
-- name    : TaitTobin.Outerplanar.outerplanar_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:10.950617+00:00
-- url     : https://prove2.me/theorems/f06f268e-c260-4c4a-b231-87613a480bd4
-- title:
--   §2, p. 5 — an outerplanar graph on n ≥ 2 vertices has at most 2n − 3 edges and no K₂,₃ subgraph
-- statement:
--   Let $G$ be an outerplanar graph on $n \ge 2$ vertices. Then
--   $$e(G) \le 2n - 3,$$
--   and $G$ does not contain the complete bipartite graph $K_{2,3}$ as a subgraph.
--
--   These two consequences of outerplanarity are the only properties of the class used in the proofs of Lemmas 4–6 and Theorem 7.
--
--   **Formalization Note** The hypothesis $n \ge 2$ is added because $2n-3$ is negative for $n \le 1$ (and natural-number subtraction would turn it into $0$). "Does not contain $K_{2,3}$ as a subgraph" is Mathlib's `Free`: there is no injective homomorphism from $K_{2,3}$ into $G$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 5, §2, second paragraph ("Two consequences of G being outerplanar …")

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace TaitTobin.Outerplanar

open Classical WangKangXue.SpectralTuran

/-- §2, p. 5: an outerplanar graph on `n ≥ 2` vertices has at most `2n - 3` edges and contains
no copy of `K₂,₃`. -/
theorem outerplanar_facts {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G) :
    G.edgeFinset.card ≤ 2 * n - 3 ∧ (completeBipartiteGraph (Fin 2) (Fin 3)).Free G := by sorry
end TaitTobin.Outerplanar
