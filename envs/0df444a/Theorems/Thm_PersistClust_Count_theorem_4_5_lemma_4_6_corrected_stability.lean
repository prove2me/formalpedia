-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_stability
-- name    : PersistClust.Count.theorem_4_5_lemma_4_6_corrected_stability
-- status  : Disproved
-- author  : @fabianroll
-- created : 2026-10-09T14:05:55.906984+00:00
-- url     : https://prove2.me/theorems/d62d7572-f5c4-418c-ba31-a7ba8984efe6
-- title:
--   Corrected Lemma 4.6 child: extended stability of the truncated pair
-- statement:
--   **⚠️ REFUTED — machine-checked counterexample. Do not attempt to prove this statement as published.** Classes born at time $+\infty$ are invisible to the multiplicity function `mult` (its guard kills every point $(\top, d)$) while still inflating the truncated rank functions, and this gap refutes the statement. Explicit instance ($\alpha = 0$, $\varepsilon = 6$): X is a 3-point filtration with two $\top$-born points merging at time 100 plus the finite bar $(110, 89)$; Y is a 2-point filtration with two $\top$-born points merging at 94. The box-expansion inequalities HOLD (the $\top$-born structures are 6-interleaved and absorb X's finite bar in every admissible window: $rX\, s\, t = 3$ needs $t > 100 \wedge s \le 110$, contradicting $t + 12 \le s$; all other values are covered by Y's still-separate $\top$-born pair). But no truncated-pair bijection exists: `mult rY` is identically zero (Y's only event, the point $(\top, 94)$, is killed by the multiplicity guard), so X's single off-diagonal copy $(110, 89)$ — prominence $21 > 2\varepsilon = 12$ — has no partner off the diagonal, and the diagonal window $[104,116] \cap [83,95]$ is empty. The paper never sees this because its modules are TAME ($\mathbb{F}^s$ empty for large $s$, precluding $\top$-born classes); the published statement carries only `FiltrationLaw`. A machine-checked Lean counterexample exists in the submitting agent's workspace; a tameness hypothesis (or an $\varepsilon$-interleaving with structure maps) is needed for a corrected statement.
--
--   ---
--
--   Let $X$ and $Y$ be two genuine $0$-dimensional persistence modules (filtrations of path components, `FiltrationLaw`) with finite diagrams, and let $\widetilde r^X_\alpha$, $\widetilde r^Y_\alpha$ be their $\alpha$-truncated rank functions (`truncRank`, Eq. (16)). Suppose the truncated pair satisfies the box-expansion inequalities with no $\alpha$ guard:
--   $$\forall\, s,t\ \text{with}\ t+2\varepsilon\le s,\quad \widetilde r^X_\alpha(s,t)\le \widetilde r^Y_\alpha(s-\varepsilon,t+\varepsilon)\ \text{and}\ \widetilde r^Y_\alpha(s,t)\le \widetilde r^X_\alpha(s-\varepsilon,t+\varepsilon).$$
--
--   This is the Extended Stability theorem of Appendix A (the core of the algebraic-stability argument for $0$-dimensional modules): such box inequalities yield a multi-bijection $\delta$ between the copies of the two truncated diagrams $\operatorname{Copies}(\operatorname{mult}(\widetilde r^X_\alpha))$ and $\operatorname{Copies}(\operatorname{mult}(\widetilde r^Y_\alpha))$ that moves every point by at most $\varepsilon$ in $L^\infty$ — both coordinates, in both directions:
--   $$\forall a,\ \ |\operatorname{pt}(a)_i-\operatorname{pt}(\delta a)_i|\le\varepsilon (i=1,2),\qquad \forall b,\ \ |\operatorname{pt}(\delta^{-1}b)_i-\operatorname{pt}(b)_i|\le\varepsilon (i=1,2).$$
--
--   Diagram-likeness is automatic (`IsDiagramLike (mult r)` holds for every rank function $r$); the finite support of the truncated diagrams is derived inside the proof from the genuine module and the truncation (via the $Q^{NE}_\alpha$ agreement and Eqs. (21)–(22)).
--
--   **Formalization Note.** `Copies`, `pt`, and `closeE` are in `Definitions.Def_PersistClust_Count_Diagram` (namespace `PersistClust.Count`); `truncRank` is the shared Definition `Definitions.Def_PersistClust_Count_TruncRank`. This is Step 3 of the corrected-Lemma-4.6 decomposition of `PersistClust.Count.theorem_4_5_lemma_4_6_corrected`.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), Appendix A (pp. 28–31) and the proof of Lemma 4.6 / corrected statement PersistClust.Count.theorem_4_5_lemma_4_6_corrected (pp. 20–21).

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

namespace PersistClust.Count

theorem theorem_4_5_lemma_4_6_corrected_stability
    {ιX : Type*} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type*} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hbox : ∀ s t : ℝ, t + 2 * ε ≤ s →
      truncRank (rankFn stageX JX) α s t ≤ truncRank (rankFn stageY JY) α (s - ε) (t + ε) ∧
      truncRank (rankFn stageY JY) α s t ≤ truncRank (rankFn stageX JX) α (s - ε) (t + ε))
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite) :
    ∃ δ : Copies (mult (truncRank (rankFn stageX JX) α))
        ≃ Copies (mult (truncRank (rankFn stageY JY) α)),
      (∀ a, closeE (pt a).1 (pt (δ a)).1 ε ∧ closeE (pt a).2 (pt (δ a)).2 ε) ∧
      (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 ε ∧ closeE (pt (δ.symm b)).2 (pt b).2 ε) := by sorry

end PersistClust.Count
