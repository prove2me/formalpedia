-- Prove2me | Theorems.Thm_WeightedEdgeColor_lemma_A_1
-- name    : WeightedEdgeColor.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:48:46.068215+00:00
-- url     : https://prove2.me/theorems/fc43daa5-d6ac-401e-afef-1f79166721e1
-- title:
--   Lemma A.1 — greedy cleanup: $\chi'_w(J)\le\lfloor4R\rfloor+1$ for weighted degree at most $R$
-- statement:
--   Let $J$ be a finite loopless weighted multigraph, with edge weights in $(0,1]$, whose maximum weighted degree is at most $R$, i.e. $W_J(v)\le R$ for every vertex $v$. Then
--   $$
--   \chi'_w(J)\le\lfloor4R\rfloor+1 ,
--   $$
--   that is, $J$ has a proper weighted coloring with $\lfloor4R\rfloor+1$ colors.
--
--   The paper uses this bound to color, with a few fresh colors, the edges left uncolored by the rounding theorem (Theorem 3.1).
--
--   **Formalization Note** Parallel edges are allowed. The number of colors is $\lfloor4R\rfloor_+ +1$ with the natural-number floor, which equals $\lfloor4R\rfloor+1$ whenever $R\ge0$; $R\ge0$ holds as soon as $J$ has a vertex.
--
--   Differences from the source:
--   - encoding: $\lfloor4R\rfloor+1$ → $\lfloor4R\rfloor_+ +1$ (natural-number floor); reason: equal for $R\ge0$; $R<0$ is possible only for a graph without vertices, where the printed bound would be negative while the empty graph needs $0$ colors
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Lemma A.1, p.24

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring

set_option autoImplicit false

namespace WeightedEdgeColor

/-- Lemma A.1 (greedy cleanup): every finite loopless weighted multigraph `J` with maximum
weighted degree at most `R` satisfies `χ′_w(J) ≤ ⌊4R⌋ + 1`.

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Lemma A.1, p.24.

**Formalization Note.** Multigraphs: parallel edges allowed (no simplicity assumption).
`χ′_w(J) ≤ ⌊4R⌋ + 1` is a proper weighted coloring into `Fin (⌊4R⌋₊ + 1)`; `⌊·⌋₊` agrees with
the integer floor for `R ≥ 0`, which holds whenever `J` has a vertex. -/
theorem lemma_A_1 (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
    (J : WGraph V E) (R : ℝ) (hR : ∀ v, J.W v ≤ R) :
    ∃ φ : E → Fin (⌊4 * R⌋₊ + 1), J.IsProperColoring φ := by sorry

end WeightedEdgeColor
