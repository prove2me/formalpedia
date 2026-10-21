-- Prove2me | Theorems.Thm_RegMatroidXC_Main_proposition_27
-- name    : RegMatroidXC.Main.proposition_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:28.743988+00:00
-- url     : https://prove2.me/theorems/5cdc88cd-e1ca-4a5e-ab79-a03800a225be
-- title:
--   Proposition 27 — every 3-connected regular matroid other than R10 has a decomposition tree without bad nodes
-- statement:
--   Let $M$ be a regular matroid with a finite ground set that is 3-connected (neither a 1-sum nor a 2-sum) and not isomorphic to $R_{10}$. Then $M$ has a **decomposition tree without bad nodes**: a finite tree $T$ whose nodes $v$ are labelled by graphic or cographic matroids $M_v$ such that
--
--   1. $M$ is obtained by performing the 3-sums $M_v \oplus_3 M_w$ over all edges $vw$ of $T$ (in arbitrary order), as in Theorem 6, and
--   2. every node $v$ whose label is not graphic has a graph $G_v$ with $M_v = M^*(G_v)$ in which each triangle $T_{uv} = E(M_v) \cap E(M_u)$ shared with a neighbour $u$ is the set $\delta(w)$ of edges at a degree-3 node $w$ of $G_v$.
--
--   This strengthening of Theorem 6 is what the cographic case of Lemma 5 (Section 6, p. 10) assumes: there, every triangle of the cographic centre of a star decomposition is the edge set at a degree-3 node.
--
--   **Formalization Note** The ambient type is infinite, so that the labels can contain fresh triangle elements outside $E(M)$; "3-connected" is the paper's definition (p. 3). Decomposition trees and bad nodes are the predicates of the `Sums` definition file.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 17, Proposition 27 (Appendix C; proof pp. 19–20)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Sums

namespace RegMatroidXC.Main

theorem proposition_27 (α : Type) [Infinite α] (M : Matroid α) [Fintype M.E] (hreg : IsRegular M)
    (h1 : ∀ M₁ M₂ : Matroid α, ¬ IsOneSum M M₁ M₂) (h2 : ∀ M₁ M₂ : Matroid α, ¬ IsTwoSum M M₁ M₂)
    (hR10 : ¬ IsR10 M) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (Ms : ι → Matroid α),
      T.IsTree ∧ (∀ v, IsGraphic (Ms v) ∨ IsCographic (Ms v)) ∧ IsDecompositionTree M T Ms ∧
      HasNoBadNodes T Ms := by sorry

end RegMatroidXC.Main
