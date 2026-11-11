-- Prove2me | Theorems.Thm_PlanarDFVSKernel_theorem_2_1
-- name    : PlanarDFVSKernel.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:58.693103+00:00
-- url     : https://prove2.me/theorems/e461b923-c107-4d82-9293-e2c10e23f72c
-- title:
--   Theorem 2.1 (Lucchesi–Younger) — min dijoin $=$ max number of disjoint directed cuts
-- statement:
--   **Theorem 2.1 (Lucchesi–Younger).** In a digraph, the minimum size of an arc set meeting every directed cut equals the maximum number of pairwise arc-disjoint directed cuts.
--
--   For every finite digraph (loops and parallel arcs allowed) there are an arc set $A$ meeting every directed cut, of minimum size among such sets, and a family $\mathcal C$ of pairwise disjoint directed cuts, of maximum size among such families, with $|A|=|\mathcal C|$.
--
--   Differences from the source:
--   - encoding: minimum size = maximum number → explicit minimizer A and maximizer 𝒞 with |A| = |𝒞|; reason: the same equality of the two extremal values
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Theorem 2.1 (Lucchesi–Younger [LY78]), p.8 (PDF 9)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_IsDirectedCut

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **Theorem 2.1 (Lucchesi–Younger)** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Theorem 2.1 (Lucchesi–Younger [LY78]), p.8 (PDF 9)):
"In a digraph, the minimum size of an arc set meeting every directed cut equals the maximum number of
pairwise arc-disjoint directed cuts."

For every finite digraph (loops and parallel arcs allowed) there are an arc set `A` meeting every
directed cut, of minimum size among such sets, and a family `𝒞` of pairwise disjoint directed cuts,
of maximum size among such families, with `|A| = |𝒞|`.

**Formalization Note** Both extremal objects are given explicitly; `|A|` is the minimum and
`|𝒞|` the maximum. A digraph without directed cuts has `A = ∅`, `𝒞 = ∅`. -/
theorem theorem_2_1 {n m : ℕ} (G : Graph n m) :
    ∃ (A : Finset (Fin m)) (𝒞 : Finset (Finset (Fin m))),
      MeetsAllDicuts G A ∧ (∀ A' : Finset (Fin m), MeetsAllDicuts G A' → A.card ≤ A'.card) ∧
      (∀ C ∈ 𝒞, IsDirectedCut G C) ∧ (𝒞 : Set (Finset (Fin m))).PairwiseDisjoint id ∧
      (∀ 𝒞' : Finset (Finset (Fin m)), (∀ C ∈ 𝒞', IsDirectedCut G C) →
        (𝒞' : Set (Finset (Fin m))).PairwiseDisjoint id → 𝒞'.card ≤ 𝒞.card) ∧
      A.card = 𝒞.card := by sorry

end PlanarDFVSKernel
