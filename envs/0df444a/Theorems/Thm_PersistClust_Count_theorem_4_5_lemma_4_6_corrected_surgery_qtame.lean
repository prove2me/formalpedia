-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_surgery_qtame
-- name    : PersistClust.Count.theorem_4_5_lemma_4_6_corrected_surgery_qtame
-- status  : Disproved
-- author  : @fabianroll
-- created : 2026-10-09T21:53:20.980024+00:00
-- url     : https://prove2.me/theorems/0e04bfc9-57ae-4780-929a-92a3c2edb119
-- title:
--   Corrected Lemma 4.6 child (q-tame): surgery lifting the truncated-pair matching to the original diagrams
-- statement:
--   **⚠️ REFUTED — machine-checked counterexample. Do not attempt to prove this statement as published.** At the explicit instance of two genuine 3-point merge-tree filtrations — X with barcode $\{(10, 0.5),\ (20, -\infty)\}$, Y with barcode $\{(10, -1),\ (20, -\infty)\}$, at $\alpha = 0$, $\varepsilon = 1$ — every hypothesis holds: the $\alpha$-truncated diagrams are $\{(10,0.5),(20,0)\}$ vs $\{(10,0),(20,0)\}$ (Y's bar $(10,-1)$, dying far below $\alpha$, clamps to the $\alpha$-row), so the truncated-pair bijection hypothesis holds (an explicit 1-close bijection both ways), as do the agreement, tameness, diagram-like and finite-support hypotheses. But the conclusion is impossible: assertion (i) demands a partner 1-close in BOTH coordinates for X's north-east point $(10, 0.5)$; Y's $(10,-1)$ (death $1.5$ away), $(20,-\infty)$ (birth $10$ away) and the diagonal ($y \in [9,11] \cap [-0.5, 1.5] = \varnothing$) all fail, so no multi-bijection $\gamma$ exists. Root cause: the truncated-pair hypothesis is blind to deaths below $\alpha$; the paper's Lemma 4.6 assumes the modules themselves are $\varepsilon$-interleaved (structure maps), which this instance violates (bottleneck $1.5 > \varepsilon$). A complete Lean counterexample (both modules, every hypothesis proven, the no-partner contradiction) is attached to the refutation submission on this theorem's qtame sibling — see its file and explanation. The same instance refutes the qtame sibling and the parent `theorem_4_5_lemma_4_6_corrected`.
--
--   ---
--
--   Let $X$ and $Y$ be two genuine $0$-dimensional persistence modules given as filtrations of path components (`FiltrationLaw`), and assume both are **q-tame**: every structure rank $r(s,t)=\\operatorname{rankFn}\\,\\mathrm{stage}\\,J\\,s\\,t$ is finite — the paper's standing assumption on persistence modules (for superlevel-set filtrations of tame functions it follows from local finiteness of component counts). Let $D^X, D^Y$ be their persistence diagrams ($\\operatorname{mult}$ of the rank function) and $\\widetilde D^X_\\alpha, \\widetilde D^Y_\\alpha$ the diagrams of the $\\alpha$-truncated rank functions (`truncRank`, Eq. (16) of Appendix A). Assume:
--   * (agreement) the diagrams agree with their truncations on the closed north-east quadrant $Q^{NE}_\\alpha$: $D(p)=\\widetilde D(p)$ for all $p\\in Q^{NE}_\\alpha$, for both modules;
--   * (matching) there is a bijection $\\delta$ between the copies of the two truncated diagrams, matching every copy to an $\\varepsilon$-close copy in both directions.
--
--   Then there is a bijection $\\gamma$ between the copies of the two ORIGINAL diagrams satisfying the four matching properties of Theorem 4.5 at threshold $\\alpha$ (`SatisfiesIIV $\\gamma$ $\\alpha$ $\\varepsilon$`):
--   $$\\exists\\,\\gamma,\\qquad \\text{SatisfiesIIV}\\;\\gamma\\;\\alpha\\;\\varepsilon.$$
--
--   This is the SURGERY step (Step 5) of the corrected Lemma 4.6 route (Appendix A): the truncated-pair stability matching is lifted to the original diagrams by composing it with vertical per-birth matchings $\\gamma_X,\\gamma_Y$ that fix the north-east quadrant pointwise (where the diagrams agree with their truncations) and move points only vertically inside the south-east part $Q^{SE}_\\alpha$. The vertical matchings exist because the two diagrams of one module have equal vertical half-line multiplicities (Eqs. (21)–(22)): the copies of $D$ with birth $b$ and death $\\le\\beta$ are as many as those of $\\widetilde D$; below the truncation line the truncated diagram concentrates all deaths on the clamped line $\\{\\mathrm{death}=\\alpha\\}$, and the concentration identity $\\sum_{d\\le\\alpha}D(b,d)=\\widetilde D(b,\\alpha)$ is exactly the window-count content of the multiplicity formula. The final clamping step matches the death-crossing copies $\\varepsilon$-proximally.
--
--   The q-tameness hypothesis is what makes the window-count route available: with all ranks finite, every bracket is $\\mathbb{N}$-valued, monotone in the probe scale, and its infimum is attained, so multiplicities count classes in windows. Without q-tameness the vertical mass lemma is not known to be provable from finiteness of the off-diagonal support alone.
--
--   **Formalization Note.** All notions live in `Definitions.Def_PersistClust_Count_Diagram` (namespace `PersistClust.Count`): `rankFn`, `mult`, `QNE`, `Copies` (off-diagonal copies indexed by $\\mathbb{N}$ below the multiplicity, plus diagonal copies $\\mathbb{R}\\times\\mathbb{N}$), `pt`, `closeE`, and the predicate `SatisfiesIIV` expressing Theorem 4.5 (i)–(iv) at threshold $\\alpha$. `truncRank` is the shared Definition `PersistClust.Count.truncRank`; `FiltrationLaw` is in `Definitions.Def_PersistClust_Count_FiltrationLaw`. Ranks are valued in $\\mathbb{N}^\\infty$, so q-tameness is stated as $r(s,t)\\ne\\top$. This is the q-tame successor of `PersistClust.Count.theorem_4_5_lemma_4_6_corrected_surgery`; Step 5 of the corrected-Lemma-4.6 decomposition of `PersistClust.Count.theorem_4_5_lemma_4_6_corrected`, consuming the q-tame stability child's bijection as its hypothesis.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), Appendix A (pp. 28–31) and the proof of Lemma 4.6 / corrected statement PersistClust.Count.theorem_4_5_lemma_4_6_corrected (pp. 20–21).

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

namespace PersistClust.Count

theorem theorem_4_5_lemma_4_6_corrected_surgery_qtame
    {ιX : Type*} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type*} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hQX : ∀ s t : ℝ, rankFn stageX JX s t ≠ ⊤)
    (hQY : ∀ s t : ℝ, rankFn stageY JY s t ≠ ⊤)
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
