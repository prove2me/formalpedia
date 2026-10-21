-- Prove2me | Theorems.Thm_RegMatroidXC_Main_theorem_6
-- name    : RegMatroidXC.Main.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:35.643047+00:00
-- url     : https://prove2.me/theorems/2c8a0f74-1bb4-4d23-a79b-b0328fc7e5c0
-- title:
--   Theorem 6 — a 3-connected regular matroid other than R10 is a tree of 3-sums of graphic and cographic matroids
-- statement:
--   Let $M$ be a regular matroid with a finite ground set that is 3-connected (neither a 1-sum nor a 2-sum) and not isomorphic to $R_{10}$. Then there is a finite tree $T$ and, for every node $v$, a matroid $M_v$ that is graphic or cographic, such that $T$ with these labels is a **decomposition tree** of $M$: every edge $vw$ of $T$ carries a 3-sum $M_v \oplus_3 M_w$, and $M$ is the matroid obtained by performing all these 3-sums (in arbitrary order).
--
--   This refinement of Seymour's decomposition theorem, with 3-sums only, is the input to the proof of Lemma 4.
--
--   **Formalization Note** The ambient type $\alpha$ is infinite, so that the parts may use elements outside $E(M)$; "not a 1-sum or 2-sum" quantifies over all pairs of matroids on $\alpha$. "Performing all 3-sums" is expressed through the cycles: $E(M)$ is the set of elements in exactly one $E(M_v)$, and the cycles of $M$ are the symmetric differences of cycles of the $M_v$ that lie in $E(M)$.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 3, Theorem 6 (proof in Appendix B, pp. 15–17)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Sums

namespace RegMatroidXC.Main

theorem theorem_6 (α : Type) [Infinite α] (M : Matroid α) [Fintype M.E] (hreg : IsRegular M)
    (h1 : ∀ M₁ M₂ : Matroid α, ¬ IsOneSum M M₁ M₂) (h2 : ∀ M₁ M₂ : Matroid α, ¬ IsTwoSum M M₁ M₂)
    (hR10 : ¬ IsR10 M) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (Ms : ι → Matroid α),
      T.IsTree ∧ (∀ v, IsGraphic (Ms v) ∨ IsCographic (Ms v)) ∧ IsDecompositionTree M T Ms := by sorry

end RegMatroidXC.Main
