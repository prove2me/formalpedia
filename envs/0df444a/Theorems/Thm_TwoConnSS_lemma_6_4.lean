-- Prove2me | Theorems.Thm_TwoConnSS_lemma_6_4
-- name    : TwoConnSS.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:42.833795+00:00
-- url     : https://prove2.me/theorems/78fb3a22-e945-461e-b90a-e50ee63c4b24
-- title:
--   Lemma 6.4 — a minimum triangle-free 2-edge-cover in polynomial time
-- statement:
--   There is a polynomial-time algorithm that, on every simple graph $G$ admitting a triangle-free 2-edge-cover, returns a triangle-free 2-edge-cover $S$ of $G$ with
--   $$|S| \le |F| \quad\text{for every triangle-free 2-edge-cover } F \text{ of } G.$$
--
--   This is the starting point of both algorithms: since every 2ECSS on at least four vertices is a triangle-free 2-edge-cover, the result is a lower bound on $\mathrm{opt}_E(G)$. The result is cited from Hartvigsen [17] and Kobayashi–Noguchi [27].
--
--   Differences from the source:
--   - encoding: a minimum triangle-free 2-edge-cover → a triangle-free 2-edge-cover of size at most that of every triangle-free 2-edge-cover; reason: same instances; avoids an infimum
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4`, fixed before the instance, on the encodings `encIn`/`encOut` (n in unary, then the adjacency matrix; edge lists in binary); reason: Lean needs a machine model; the input length is at least n², so polynomial in the code length is polynomial in n
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Lemma 6.4, p.25 (PDF p.26), citing [17, 27]

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_IsTwoEdgeCover

namespace TwoConnSS

/-- **Lemma 6.4 ([17, 27]): a minimum triangle-free 2-edge-cover in polynomial time.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Lemma 6.4, p.25: "A minimum
triangle-free 2-edge-cover in a simple graph admitting such a cover can be computed in polynomial
time."

There is a polynomial-time `alg` such that, on every instance whose graph `G` has a triangle-free
2-edge-cover, the output is a triangle-free 2-edge-cover of `G` with at most `|F|` edges for every
triangle-free 2-edge-cover `F` of `G`.

**Formalization Note.** "Triangle-free" excludes triangle components only (p.25). The result is
cited from [17, 27]. Machines as in Theorem 5.1. -/
theorem lemma_6_4 :
    ∃ alg : Inst → List (ℕ × ℕ), Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
      ∀ I : Inst, (∃ F, IsTwoEdgeCover I.graph F ∧ IsTriangleFree F) →
        IsTwoEdgeCover I.graph (toEdges I.n (alg I)) ∧ IsTriangleFree (toEdges I.n (alg I)) ∧
        ∀ F, IsTwoEdgeCover I.graph F → IsTriangleFree F → (toEdges I.n (alg I)).card ≤ F.card := by sorry

end TwoConnSS
