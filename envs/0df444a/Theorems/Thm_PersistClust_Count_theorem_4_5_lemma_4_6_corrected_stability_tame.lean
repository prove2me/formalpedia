-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_stability_tame
-- name    : PersistClust.Count.theorem_4_5_lemma_4_6_corrected_stability_tame
-- status  : Open
-- author  : @fabianroll
-- created : 2026-10-09T17:52:48.512354+00:00
-- url     : https://prove2.me/theorems/a156447d-0371-490a-8454-bff38ae7dd8c
-- title:
--   Lemma 4.6 (corrected), stability step with tameness: box expansion for truncated ranks of tame modules yields an ε-multi-bijection of the truncated diagrams
-- statement:
--   This is the tameness-corrected form of the stability step of Lemma 4.6 of the paper (p. 21; proof in Appendix A), the algebraic-stability ingredient of Theorem 4.5.
--
--   Let $X$ and $Y$ be tame 0-dimensional persistence modules, encoded by stage families $\mathrm{stage}_X, \mathrm{stage}_Y : \mathbb{R} \to \mathrm{Set}(\iota)$ decreasing in the threshold, and component relations $J_X, J_Y$. Tameness means that the stages eventually vanish: $\exists s_0\, \forall s \ge s_0,\ \mathrm{stage}(s) = \varnothing$. Write $r_X = \operatorname{rankFn}(\mathrm{stage}_X, J_X)$ and $r_Y = \operatorname{rankFn}(\mathrm{stage}_Y, J_Y)$ for the rank functions, and $\widetilde r_X = \operatorname{truncRank}(r_X, \alpha)$, $\widetilde r_Y = \operatorname{truncRank}(r_Y, \alpha)$ for their $\alpha$-truncations (the rank functions restricted to the quadrant $[\alpha, \infty)^2$).
--
--   Assume the persistence diagrams of $r_X$ and $r_Y$ have finite support, and that the truncated rank functions satisfy the box-expansion inequalities with no $\alpha$-guard: for all $s, t \in \mathbb{R}$ with $t + 2\varepsilon \le s$,
--
--   $$\widetilde r_X(s, t) \le \widetilde r_Y(s - \varepsilon,\, t + \varepsilon), \qquad \widetilde r_Y(s, t) \le \widetilde r_X(s - \varepsilon,\, t + \varepsilon).$$
--
--   Then there exists a multi-bijection $\delta$ between the copies of the two truncated diagrams $\operatorname{mult}(\widetilde r_X)$ and $\operatorname{mult}(\widetilde r_Y)$ that moves every point by at most $\varepsilon$ in the $L^\infty$ norm, in both coordinates and both directions.
--
--   The tameness hypothesis is necessary: without it, $+\infty$-born classes are invisible to the diagram (the off-diagonal multiplicity guard discards points with infinite birth coordinate) while still inflating the truncated rank functions, so the box inequalities can hold for rank functions whose truncated diagrams are fundamentally incomparable (one empty, the other not) — a machine-checked counterexample exists for the untamed sibling statement. With tameness (satisfied by the superlevel and Rips modules appearing in Theorem 4.5), the Extended-Stability argument of Appendix A applies.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968, 2009, pp. 20–21, Lemma 4.6 and Appendix A; algebraic stability: Chazal–Cohen-Steiner–Glisse–Oudot, https://hal.inria.fr/inria-00160683

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

namespace PersistClust.Count

theorem theorem_4_5_lemma_4_6_corrected_stability_tame
    {ιX : Type*} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type*} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : ∃ s₀ : ℝ, ∀ s ≥ s₀, stageX s = ∅)
    (hTameY : ∃ s₀ : ℝ, ∀ s ≥ s₀, stageY s = ∅)
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
