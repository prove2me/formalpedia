-- Prove2me | Theorems.Thm_RegMatroidXC_Main_lemma_5
-- name    : RegMatroidXC.Main.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:58.587901+00:00
-- url     : https://prove2.me/theorems/abc09bdd-3699-4fa4-baa0-2b512b76f0b9
-- title:
--   Lemma 5 (with the standing assumption of Section 6, p. 10) — xc(P(M)) ≤ c₁|E(M₀)|² + 16 Σᵢ xc(P(Mᵢ))
-- statement:
--   There is an absolute constant $c_1$ with the following property. Let $M$ be a loopless matroid with a star decomposition $M \overset{\star}{=} M_0 \oplus_3 M_1 \oplus_3 \cdots \oplus_3 M_k$ in which $M_0$ is graphic or cographic, $M_1, \dots, M_k$ are mutually disjoint regular matroids, and, if $M_0$ is not graphic, $M_0 = M^*(G)$ for a connected graph $G$ with every triangle $T_i$ the set of edges at a degree-3 node. Then
--   $$\mathrm{xc}(P(M)) \le c_1 \cdot |E(M_0)|^2 + 16 \sum_{i=1}^k \mathrm{xc}(P(M_i)).$$
--   Precisely: if each $P(M_i)$ has an extended formulation with $r_i$ inequalities, then $P(M)$ has one with at most $c_1 |E(M_0)|^2 + 16 \sum_i r_i$ inequalities.
--
--   Together with Lemma 4, this bound drives the induction proving that $\mathrm{xc}(P(M)) = O(n^6)$ for regular $M$.
--
--   **Formalization Note** The vertex-star clause for cographic $M_0$ is the assumption under which Section 6 (p. 10) proves the cographic case; the printed Lemma 5 does not state it, and its proof does not cover the case without it. Looplessness is the paper's standing assumption (end of §4.1, p. 5), used in the proof through the description of $P(M)$ by connected flats. The constant $c_1$ is chosen before the matroids.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 2, Lemma 5 (proof p. 12, from Propositions 15, 16, 18); standing assumptions p. 5 (§4.1) and p. 10 (Section 6)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Sums
open ExtensionComplexity.TSP

namespace RegMatroidXC.Main

theorem lemma_5 : ∃ c₁ : ℝ, ∀ (α : Type) (M M₀ : Matroid α) (k : ℕ) (Ms : Fin k → Matroid α)
    [Fintype M.E] [Fintype M₀.E] [∀ i, Fintype (Ms i).E],
    M.Loopless → (IsGraphic M₀ ∨ IsCographic M₀) → (∀ i, IsRegular (Ms i)) →
    IsStarDecomposition M M₀ Ms → TrianglesAreVertexStars M₀ Ms →
    ∀ r : Fin k → ℕ, (∀ i, IsEFOfSize (indepPolytope (Ms i)) (r i)) →
      ∃ r₀ : ℕ, IsEFOfSize (indepPolytope M) r₀ ∧
        (r₀ : ℝ) ≤ c₁ * (Fintype.card M₀.E : ℝ) ^ 2 + 16 * ∑ i, (r i : ℝ) := by sorry

end RegMatroidXC.Main
