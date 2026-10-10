-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected
-- name    : PersistClust.Count.theorem_4_5_lemma_4_6_corrected
-- status  : Disproved
-- author  : @fabianroll
-- created : 2026-10-09T11:27:34.782897+00:00
-- url     : https://prove2.me/theorems/c9d424dd-4b56-4237-abaf-c19e48f0a586
-- title:
--   Lemma 4.6 (corrected): box-expansion interleaving above α of filtration rank functions yields the multi-bijection (i)–(iv)
-- statement:
--   **⚠️ REFUTED — machine-checked counterexample. Do not attempt to prove this statement as published.** The rank-interleaving hypothesis (with the $\alpha$ guard) is strictly weaker than the paper's strong module interleaving, and the gap is fatal. At the explicit instance — X with barcode $\{(10, 0.5),\ (20, -\infty)\}$, Y with barcode $\{(10, -1),\ (20, -\infty)\}$, $\alpha = 0$, $\varepsilon = 1$ — the rank-window inequalities HOLD (both directions: X's thin bar contributes only at windows with $t + 2\varepsilon \le s \le 10$, forcing $t \le 8$, where Y's $(10,-1)$ bar covers the shifted comparison; the essential-bar corners are excluded by $t \le s - 2\varepsilon \le 18$), and all diagram-like / finite-support hypotheses hold; yet the conclusion fails — X's north-east point $(10, 0.5)$ has no 1-close partner among Y's copies (deaths/births too far, diagonal window empty). The window $t + 2\varepsilon \le s$ with $t \ge \alpha$ never probes deaths below $\alpha$, so a Y-bar dying far below $\alpha$ is invisible to the hypothesis while remaining unmatched in the conclusion. A complete Lean counterexample artifact is attached to the refutation submission on the qtame surgery child of this theorem.
--
--   ---
--
--   This is the corrected form of Lemma 4.6 of the paper (p. 21; proof in Appendix A), the algebraic-stability ingredient of Theorem 4.5.
--
--   Let $r_X$ and $r_Y$ be the rank functions of two tame 0-dimensional persistence modules, given in the Lean encoding as $r_X = \operatorname{rankFn}(\mathrm{stage}_X, J_X)$ and $r_Y = \operatorname{rankFn}(\mathrm{stage}_Y, J_Y)$, where the stage families decrease with the threshold parameter and each $J_t$ is the "same component of $\mathrm{stage}(t)$" equivalence, compatible with the inclusions (the hypothesis `FiltrationLaw` — exactly the structural law of a genuine filtration). Assume the diagrams $\operatorname{mult} r_X$, $\operatorname{mult} r_Y$ are diagram-like with finite off-diagonal support, and that the modules are strongly $\varepsilon$-interleaved above the level $\alpha$, expressed in rank form: for all $s \ge t + 2\varepsilon$ with $t \ge \alpha$,
--   $$r_X(s,t) \le r_Y(s-\varepsilon,\,t+\varepsilon) \qquad\text{and}\qquad r_Y(s,t) \le r_X(s-\varepsilon,\,t+\varepsilon).$$
--   Then there exists a multi-bijection $\gamma$ between the off-diagonal copies of the two diagrams satisfying assertions (i)–(iv) of Theorem 4.5: $\gamma$ and $\gamma^{-1}$ displace every point of the quadrant $Q^{NE}_\alpha$ by at most $\varepsilon$ in each coordinate, and every point of the quadrant $Q^{SE}_\alpha$ by at most $\varepsilon$ in its first coordinate.
--
--   This is the reusable algebraic-stability lemma for Theorem 4.5; it is consumed by the parent reduction together with the geometric interleaving child that supplies its hypotheses for the superlevel-set and Rips filtrations.
--
--   **Formalization Note.** The `FiltrationLaw` hypothesis is essential: with only the rank inequalities (even in the box-expansion form) together with diagram-likeness and finite support, the statement is false. The multiplicity at an essential point $(b,-\infty)$ takes an infimum over all $\varepsilon > 0$ and thereby probes ranks at levels below $\alpha$, where the interleaving imposes no constraint; non-monotone rank functions can satisfy the inequalities while the conclusion fails. `FiltrationLaw` excludes such pathological functions and is provable for the two rank functions of Theorem 4.5.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968, 2009, pp. 20–21, Lemma 4.6 (proof in Appendix A); algebraic stability: Chazal–Cohen-Steiner–Glisse–Oudot, https://hal.inria.fr/inria-00160683

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw

namespace PersistClust.Count

theorem theorem_4_5_lemma_4_6_corrected
    {ιX : Type*} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type*} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hbx : ∀ s t : ℝ, t + 2 * ε ≤ s → α ≤ t →
      rankFn stageX JX s t ≤ rankFn stageY JY (s - ε) (t + ε) ∧
      rankFn stageY JY s t ≤ rankFn stageX JX (s - ε) (t + ε))
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite) :
    ∃ γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY JY)),
      SatisfiesIIV γ α ε := by sorry

end PersistClust.Count
