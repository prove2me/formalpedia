-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected_stability_qtame
-- name    : PersistClust.Count.theorem_4_5_lemma_4_6_corrected_stability_qtame
-- status  : Disproved
-- author  : @fabianroll
-- created : 2026-10-09T21:43:46.201883+00:00
-- url     : https://prove2.me/theorems/d13ac7f3-db8d-4c1e-a879-5ff261f43c68
-- title:
--   Corrected Lemma 4.6 child (q-tame): box inequalities give an eps-matching of truncated diagrams
-- statement:
--   **⚠️ REFUTED — machine-checked counterexample. Do not attempt to prove this statement as published.** At the explicit instance of two genuine 3-point merge-tree filtrations — X with barcode $\{(5,-\infty),\ (4.2, 0.5),\ (2.5, -0.6)\}$, Y with barcode $\{(5,-\infty),\ (3.2, -1.5),\ (1.6, 0.3)\}$, at $\alpha = -2$, $\varepsilon = 1$ — every hypothesis holds, including the box-expansion inequalities for the TRUNCATED ranks with no $\alpha$ guard (verified through every multiplicity and rank-window computation). But the asserted multi-bijection of the truncated diagrams is impossible: X's truncated bar $(4.2, 0.5)$ has no 1-close partner among Y's truncated support $\{(5,-2), (3.2,-1.5), (1.6,0.3)\}$ (each candidate fails a $\ell_\infty$ corner) nor on the diagonal ($y \in [3.2, 5.2] \cap [-0.5, 1.5] = \varnothing$). Root cause: rank-level box inequalities are a strictly weaker CONSEQUENCE of the paper's strong module interleaving (with structure maps); they cannot certify a copy-level $\varepsilon$-bijection. A complete machine-checked Lean counterexample (97 declarations, zero sorries) exists in the submitting agent's workspace.
--
--   ---
--
--   Let $X$ and $Y$ be two genuine $0$-dimensional persistence modules given as filtrations of path components: $\\mathrm{stage}:\\mathbb{R}\\to\\mathrm{Set}\\,\\iota$ is a decreasing family of sets and $J_t$ is the \"same component of $\\mathrm{stage}(t)$\" equivalence, compatible with the inclusions $\\mathrm{stage}(t)\\subseteq\\mathrm{stage}(s)$ for $s\\le t$ (`FiltrationLaw`). Assume both modules are **q-tame**: every structure rank is finite,
--   $$\\forall\\, s,t\\in\\mathbb{R},\\qquad r^X(s,t)<\\infty\\quad\\text{and}\\quad r^Y(s,t)<\\infty,$$
--   the paper's standing assumption on persistence modules (for superlevel-set filtrations of tame functions it follows from local finiteness of component counts). Let $\\widetilde r^X_\\alpha,\\widetilde r^Y_\\alpha$ be the $\\alpha$-truncated rank functions ($\\widetilde r(s,t)=r(s,t)$ if $\\alpha\\le s$ and $\\alpha\\le t$, and $0$ otherwise; Eq. (16) of Appendix A), with truncated diagrams $\\widetilde D^X_\\alpha,\\widetilde D^Y_\\alpha$. Suppose the truncated pair satisfies the box-expansion inequalities with no $\\alpha$ guard:
--   $$\\forall\\, s,t\\ \\text{with}\\ t+2\\varepsilon\\le s,\\quad \\widetilde r^X_\\alpha(s,t)\\le\\widetilde r^Y_\\alpha(s-\\varepsilon,t+\\varepsilon)\\ \\text{and}\\ \\widetilde r^Y_\\alpha(s,t)\\le\\widetilde r^X_\\alpha(s-\\varepsilon,t+\\varepsilon).$$
--
--   This is the Extended Stability theorem of Appendix A, the core of the algebraic-stability argument for $0$-dimensional modules: such box inequalities yield a multi-bijection $\\delta$ between the copies of the two truncated diagrams, matching every copy of $\\widetilde D^X_\\alpha$ to an $\\varepsilon$-close copy of $\\widetilde D^Y_\\alpha$ and conversely:
--   $$\\exists\\ \\delta,\\qquad \\forall\\,a,\\ |\\mathrm{pt}(a)_1-\\mathrm{pt}(\\delta a)_1|\\le\\varepsilon\\ \\wedge\\ |\\mathrm{pt}(a)_2-\\mathrm{pt}(\\delta a)_2|\\le\\varepsilon,\\quad\\text{and likewise for $\\delta^{-1}$.}$$
--
--   The q-tameness hypothesis is essential for the known proof route: the per-point agreement of a diagram with its $\\alpha$-truncation — the entry step of the route — is FALSE for non-q-tame modules even with finite off-diagonal support and stage-tameness (a countable bar collapses the original bracket infimum through $\\infty-\\infty$ while the truncated bracket stays positive). For q-tame modules the route is complete: the agreement step is the sibling lemma (diagram-truncation agreement, q-tame form), the rectangle-count inequality follows from the window-count interpretation of multiplicities (monotone brackets, attained infima over $\\mathbb{N}$-valued terms), and Hall's theorem assembles the multi-bijection with the diagonal absorbing the surplus of short bars.
--
--   **Formalization Note.** All notions live in `Definitions.Def_PersistClust_Count_Diagram` (namespace `PersistClust.Count`): `rankFn`, `mult`, `QNE`, `Copies` (the copy index set of a diagram, off-diagonal copies indexed by $\\mathbb{N}$ below the multiplicity plus diagonal copies $\\mathbb{R}\\times\\mathbb{N}$), `pt` (the point of a copy) and `closeE` (the $\\varepsilon$-closeness predicate on the extended line). `truncRank` is the shared Definition `PersistClust.Count.truncRank`; `FiltrationLaw` is in `Definitions.Def_PersistClust_Count_FiltrationLaw`. Ranks are valued in $\\mathbb{N}^\\infty$, so q-tameness is stated as $r(s,t)\\ne\\top$. This is the q-tame successor of `PersistClust.Count.theorem_4_5_lemma_4_6_corrected_stability_tame` (whose stage-tameness hypothesis does not imply q-tameness and whose proof route requires the q-tame agreement step); Step 1 of the corrected-Lemma-4.6 decomposition of `PersistClust.Count.theorem_4_5_lemma_4_6_corrected`.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), Appendix A (pp. 28–31) and the proof of Lemma 4.6 / corrected statement PersistClust.Count.theorem_4_5_lemma_4_6_corrected (pp. 20–21).

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

namespace PersistClust.Count

theorem theorem_4_5_lemma_4_6_corrected_stability_qtame
    {ιX : Type*} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type*} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hQX : ∀ s t : ℝ, rankFn stageX JX s t ≠ ⊤)
    (hQY : ∀ s t : ℝ, rankFn stageY JY s t ≠ ⊤)
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
