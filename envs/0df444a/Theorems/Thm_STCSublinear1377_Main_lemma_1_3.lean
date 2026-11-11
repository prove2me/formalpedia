-- Prove2me | Theorems.Thm_STCSublinear1377_Main_lemma_1_3
-- name    : STCSublinear1377.Main.lemma_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:12.051567+00:00
-- url     : https://prove2.me/theorems/8d78e7fa-0d65-4cc2-86be-330922912bdf
-- title:
--   Lemma 1.3 — Hereditary-bisection edge and vertex load algorithm
-- statement:
--   Let $F$ be a connected positive-integer-weighted graph on $n\ge1$ vertices, with total edge weight $M$ and hereditary bisection $B$. There is a uniform algorithm, polynomial in $n+M$, returning a spanning tree whose edge and endpoint-inclusive vertex loads satisfy
--
--   $$c_{F,T}(e)\le C B(\log n)^{3/2},\qquad
--   \ell_{F,T}(v)\le C B(\log n)^{3/2}.$$
--
--   The same output tree satisfies both bounds. The randomized bisection calls can be amplified for each fixed $r>0$ so this common event has probability at least $1-n^{-r}$. Every tape returns a spanning tree. For a singleton graph there are no demands and both loads are zero. This is the edge-and-vertex version used for internal trees, not merely an edge-congestion approximation.
--
--   **Formalization Note** Unary total-weight padding charges polynomial dependence on $M$. Hereditary bisection ranges over all subgraphs, including edge deletions. No numerical hidden constant is specified by the paper.
--
--   Differences from the source:
--   - encoding: an arbitrary finite graph → a binary adjacency table on Fin n; reason: every finite graph can be enumerated, and symmetry and absence of loops are checked explicitly
--   - reading: an algorithm using the hereditary-bisection approximation, with amplification specified later → a finite fair-tape algorithm with a common high-probability event for both load bounds; reason: the final paragraph on p.15 explicitly amplifies randomized bisection calls for every fixed confidence exponent
--   - encoding: time polynomial in n plus total edge weight → a polynomial-time TM2 evaluator on an encoding padded by the total edge weight; reason: this preserves dependence on M rather than replacing it by logarithmic dependence
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Lemma 1.3, PDF/printed p.3; Appendix A.2 p.18; amplification convention in §3.4 p.15

import Definitions.Def_STCSublinear1377_Main_DataMachine
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- The unary total-weight padding implements exactly the stated polynomial(n + M) resource
parameter. Singleton trees have no demands and zero edge and vertex loads. -/
theorem lemma_1_3 :
    ∀ r : ℝ, 0 < r → ∃ a : RandomDataMachine, ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ f : WeightedGraph n,
        f.vertices = Finset.univ → f.positive → f.integral → f.connected →
        let input := unaryGraphBits f
        (∀ tape : Fin (a.tapeLength input) → Bool,
          let out := a.output input tape
          out.length = n * n ∧ f.tree (outputTable n out)) ∧
        dataProbability a input (fun out =>
          let t := outputTable n out
          let bound := C * f.hereditaryBisection * Real.rpow (Real.log (n : ℝ)) (3 / 2 : ℝ)
          (∀ u v, t u v = true → f.edgeLoad t u v ≤ bound) ∧
          (∀ v ∈ f.vertices, f.vertexLoad t v ≤ bound)) ≥
            1 - Real.rpow (n : ℝ) (-r) := by sorry

end STCSublinear1377.Main
