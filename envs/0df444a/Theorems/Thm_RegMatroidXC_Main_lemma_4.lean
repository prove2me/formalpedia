-- Prove2me | Theorems.Thm_RegMatroidXC_Main_lemma_4
-- name    : RegMatroidXC.Main.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:21.023164+00:00
-- url     : https://prove2.me/theorems/e742be4d-4b62-4ce4-8ef2-7d1a657242f9
-- title:
--   Lemma 4 (with the decomposition of Proposition 27, p. 17) — star decomposition with k ≤ n/4 and |E(Mᵢ)| ≤ n/2 + 3
-- statement:
--   Let $M$ be a regular matroid on $n$ elements that is neither graphic, nor cographic, nor isomorphic to $R_{10}$, and that is neither a 1-sum nor a 2-sum. Then there are matroids $M_0, M_1, \dots, M_k$ with
--   $$1 \le k \le \frac n4$$
--   such that
--
--   1. $M_0$ is graphic or cographic and $|E(M_0)| \le n$;
--   2. $M_1, \dots, M_k$ are mutually disjoint regular matroids with $|E(M_i)| \le n/2 + 3$ for every $i$;
--   3. $M$ is obtained from $M_0$ by simultaneously performing a 3-sum with each $M_i$ (a star decomposition $M \overset{\star}{=} M_0 \oplus_3 M_1 \oplus_3 \cdots \oplus_3 M_k$);
--   4. (from Proposition 27) if $M_0$ is not graphic, then $M_0 = M^*(G)$ for a connected graph $G$ and every triangle $T_i = E(M_0) \cap E(M_i)$ is the set of edges at a node of $G$ of degree 3.
--
--   The star decomposition is the inductive step of the main theorem for 3-connected matroids; clause 4 is the form in which Lemma 5's cographic case (Section 6) needs it.
--
--   **Formalization Note** Clause 4 is not printed in Lemma 4: Section 6 (p. 10) assumes it, citing Proposition 27, whose decomposition tree without bad nodes makes the proof of Lemma 4 produce it. The bounds $k \le n/4$ and $|E(M_i)| \le n/2 + 3$ are read over $\mathbb R$. The ambient type is infinite so that triangle elements outside $E(M)$ exist.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 2, Lemma 4 (proof p. 3); clause (iv) from Section 6, p. 10 and Proposition 27, p. 17

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Sums

namespace RegMatroidXC.Main

theorem lemma_4 (α : Type) [Infinite α] (M : Matroid α) [Fintype M.E] (hreg : IsRegular M)
    (hng : ¬ IsGraphic M) (hnc : ¬ IsCographic M) (hR10 : ¬ IsR10 M)
    (h1 : ∀ M₁ M₂ : Matroid α, ¬ IsOneSum M M₁ M₂) (h2 : ∀ M₁ M₂ : Matroid α, ¬ IsTwoSum M M₁ M₂) :
    ∃ (k : ℕ) (M₀ : Matroid α) (Ms : Fin k → Matroid α),
      1 ≤ k ∧ (4 * k : ℝ) ≤ Fintype.card M.E ∧
      (IsGraphic M₀ ∨ IsCographic M₀) ∧ (M₀.E.ncard : ℝ) ≤ Fintype.card M.E ∧
      (∀ i, IsRegular (Ms i)) ∧ (∀ i, ((Ms i).E.ncard : ℝ) ≤ (Fintype.card M.E : ℝ) / 2 + 3) ∧
      IsStarDecomposition M M₀ Ms ∧ TrianglesAreVertexStars M₀ Ms := by sorry

end RegMatroidXC.Main
