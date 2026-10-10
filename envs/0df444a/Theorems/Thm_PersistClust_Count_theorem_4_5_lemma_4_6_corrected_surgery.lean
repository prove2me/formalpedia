-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_surgery
-- name    : PersistClust.Count.theorem_4_5_lemma_4_6_corrected_surgery
-- status  : Disproved
-- author  : @fabianroll
-- created : 2026-10-09T14:05:59.785183+00:00
-- url     : https://prove2.me/theorems/c50e0db1-f864-4397-938d-a072117eea84
-- title:
--   Corrected Lemma 4.6 child: surgery composition yielding SatisfiesIIV
-- statement:
--   **⚠️ REFUTED — machine-checked counterexample. Do not attempt to prove this statement as published.** At the explicit instance of two genuine 3-point merge-tree filtrations — X with barcode $\{(10, 0.5),\ (20, -\infty)\}$, Y with barcode $\{(10, -1),\ (20, -\infty)\}$, at $\alpha = 0$, $\varepsilon = 1$ — every hypothesis holds: the $\alpha$-truncated diagrams are $\{(10,0.5),(20,0)\}$ vs $\{(10,0),(20,0)\}$ (Y's bar $(10,-1)$, dying far below $\alpha$, clamps to the $\alpha$-row), so the truncated-pair bijection hypothesis holds (an explicit 1-close bijection both ways), as do the agreement, tameness, diagram-like and finite-support hypotheses. But the conclusion is impossible: assertion (i) demands a partner 1-close in BOTH coordinates for X's north-east point $(10, 0.5)$; Y's $(10,-1)$ (death $1.5$ away), $(20,-\infty)$ (birth $10$ away) and the diagonal ($y \in [9,11] \cap [-0.5, 1.5] = \varnothing$) all fail, so no multi-bijection $\gamma$ exists. Root cause: the truncated-pair hypothesis is blind to deaths below $\alpha$; the paper's Lemma 4.6 assumes the modules themselves are $\varepsilon$-interleaved (structure maps), which this instance violates (bottleneck $1.5 > \varepsilon$). A complete Lean counterexample (both modules, every hypothesis proven, the no-partner contradiction) is attached to the refutation submission on this theorem's qtame sibling — see its file and explanation. The same instance refutes the qtame sibling and the parent `theorem_4_5_lemma_4_6_corrected`.
--
--   ---
--
--   Let $X$ and $Y$ be two genuine $0$-dimensional persistence modules (`FiltrationLaw`) with finite diagrams, $\alpha\in\mathbb{R}$, $\varepsilon\ge0$. Write $D_X=\operatorname{mult}(r^X)$, $D_Y=\operatorname{mult}(r^Y)$ for the original diagrams and $\widetilde D^X_\alpha$, $\widetilde D^Y_\alpha$ for the $\alpha$-truncated diagrams. Assume:
--   (a) the original and truncated diagrams agree on the closed north-east quadrant $Q^{NE}_\alpha=(\alpha,+\infty]\times(\alpha,+\infty]$ ($\operatorname{mult}(r)(p)=\operatorname{mult}(\widetilde r_\alpha)(p)$ for $p\in Q^{NE}_\alpha$, for each module); and
--   (b) a multi-bijection $\delta$ of the truncated diagrams with $L^\infty$-$\varepsilon$ control (both coordinates, both directions).
--
--   Then there is a multi-bijection $\gamma$ of the ORIGINAL diagrams $\operatorname{Copies}(D_X)\simeq\operatorname{Copies}(D_Y)$ satisfying assertions (i)–(iv) of Theorem 4.5 at threshold $\alpha$ and radius $\varepsilon$ (`SatisfiesIIV γ α ε`): on $Q^{NE}_\alpha$ both coordinates of the matched point are $\varepsilon$-close (both directions); on $Q^{SE}_\alpha=(\alpha,+\infty]\times[-\infty,\alpha]$ only the first coordinate is guaranteed $\varepsilon$-close (both directions).
--
--   The construction is the SURGERY of Appendix A: $\gamma_X$ fixes $Q^{NE}_\alpha$ and moves points only vertically within $Q^{SE}_\alpha$ (the vertical half-line multiplicities of the original and truncated diagrams coincide, Eqs. (21)–(22), via the $\eta$-grid and Eq. (18)), and similarly $\gamma_Y$; one composes $\gamma_Y\circ\delta\circ\gamma_X$. **Death-crossing subtlety:** the naive composite can violate assertion (i) when $\delta$ moves a $Q^{NE}_\alpha$ point whose death lies in $(\alpha,\alpha+\varepsilon]$ to death $\alpha$ (the truncated diagram clamps deaths to $\alpha$) and $\gamma_Y^{-1}$ then moves it vertically below $\alpha-\varepsilon$; the resolution is to choose the vertical per-birth matching $\varepsilon$-proximally — match each vertical half-line of the truncated diagram to the original within vertical distance $\varepsilon$, which is possible because truncation only clamps deaths downward to $\alpha$.
--
--   **Formalization Note.** `Copies`, `pt`, `closeE`, `SatisfiesIIV`, `QNE` are in `Definitions.Def_PersistClust_Count_Diagram` (namespace `PersistClust.Count`); `truncRank` is the shared Definition `Definitions.Def_PersistClust_Count_TruncRank`. This is Step 5 of the corrected-Lemma-4.6 decomposition of `PersistClust.Count.theorem_4_5_lemma_4_6_corrected`.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), Appendix A (pp. 28–31) and the proof of Lemma 4.6 / corrected statement PersistClust.Count.theorem_4_5_lemma_4_6_corrected (pp. 20–21).

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

namespace PersistClust.Count

theorem theorem_4_5_lemma_4_6_corrected_surgery
    {ιX : Type*} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type*} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite)
    (hAgree : ∀ p ∈ QNE α, mult (rankFn stageX JX) p = mult (truncRank (rankFn stageX JX) α) p ∧
                            mult (rankFn stageY JY) p = mult (truncRank (rankFn stageY JY) α) p)
    (hδ : ∃ δ : Copies (mult (truncRank (rankFn stageX JX) α))
        ≃ Copies (mult (truncRank (rankFn stageY JY) α)),
        (∀ a, closeE (pt a).1 (pt (δ a)).1 ε ∧ closeE (pt a).2 (pt (δ a)).2 ε) ∧
        (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 ε ∧ closeE (pt (δ.symm b)).2 (pt b).2 ε)) :
    ∃ γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY JY)),
      SatisfiesIIV γ α ε := by sorry

end PersistClust.Count
