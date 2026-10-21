-- Prove2me | Theorems.Thm_RegMatroidXC_Main_proposition_12
-- name    : RegMatroidXC.Main.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:16:48.796978+00:00
-- url     : https://prove2.me/theorems/4b9e928c-46a3-48fb-8c56-8f5dd3a4820b
-- title:
--   Proposition 12 — xc(conv ⋃ᵢ Pᵢ) ≤ Σᵢ xc(Pᵢ) for polytopes of dimension at least 1
-- statement:
--   Let $P_1, \dots, P_k \subseteq \mathbb R^n$ be polytopes of dimension at least 1. Then
--   $$\mathrm{xc}\Big(\operatorname{conv} \bigcup_{i=1}^k P_i\Big) \le \sum_{i=1}^k \mathrm{xc}(P_i).$$
--   Precisely: if each $P_i$ has an extended formulation with $r_i$ inequalities, then the convex hull of their union has one with at most $r_1 + \dots + r_k$ inequalities.
--
--   This refinement of Balas's disjunctive formulation is what the proof of Lemma 5 uses to combine the formulations of the parts of a 3-sum.
--
--   **Formalization Note** "Polytope" is the convex hull of a finite set of points (the published `IsPolytope`), and "dimension at least 1" is "contains two distinct points". The ambient space is $\mathbb R^\iota$ for a finite index type $\iota$. The paper's "$P_i \in \mathbb R^n$" is read as $P_i \subseteq \mathbb R^n$.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 5, Proposition 12

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_Polytope
open ExtensionComplexity.TSP

namespace RegMatroidXC.Main

theorem proposition_12 {ι : Type} [Fintype ι] (k : ℕ) (P : Fin k → Set (ι → ℝ))
    (hP : ∀ i, IsPolytope (P i)) (hdim : ∀ i, (P i).Nontrivial)
    (r : Fin k → ℕ) (hr : ∀ i, IsEFOfSize (P i) (r i)) :
    ∃ s : ℕ, IsEFOfSize (convexHull ℝ (⋃ i, P i)) s ∧ s ≤ ∑ i, r i := by sorry

end RegMatroidXC.Main
