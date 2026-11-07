-- Prove2me | Theorems.Thm_SamplingAC0_lemma_15
-- name    : SamplingAC0.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:49:01.933545+00:00
-- url     : https://prove2.me/theorems/e4516034-b354-4b5a-bb97-ceb73f959d07
-- title:
--   Lemma 15 — restricting a forest to average Lipschitzness [AGM+26, Lemma 29]
-- statement:
--   Let $f$ be a decision forest of depth $d$ on $s$ input bits with $b$ output positions, and let $\mu>0$. There is a decision tree $T$ on the same $s$ bits, of depth at most $100bd/\mu$, such that for the leaf $\gamma$ reached by a uniform input to $T$,
--
--   $$\mathbb P_\gamma\bigl[f|_\gamma\text{ is average-}\mu\text{-Lipschitz}\bigr]\ \ge\ 0.99 .$$
--
--   Here $f|_\gamma$ is the forest restricted by the bits fixed on the path to $\gamma$. Fixing the few popular bits makes every remaining bit rarely queried on average; the lemma is the first step in the proof of Lemma 12.
--
--   **Formalization Note** The leaf $\gamma$ reached by $x$ is the restriction fixing the bits queried on $x$'s path. The mission poses this lemma; its proof is in [AGM+26], not in this paper.
--
--   Differences from the source:
--   - generalization: f : {0,1}^s → {0,1}^b → output positions any finite type ι, with b = |ι|; reason: the case ι = Fin b is the source's
--   - encoding: a 100bd/µ-depth tree; "with probability 0.99" → every path of T has at most 100bd/µ queries; probability ≥ 0.99; µ > 0; reason: 100bd/µ is undefined at µ = 0
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 15, p.11 (from [AGM+26, Lemma 29])

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_Restriction
import Definitions.Def_SamplingAC0_AvgLipschitz
set_option autoImplicit false

namespace SamplingAC0

/-- **Lemma 15 ([AGM+26, Lemma 29]): restricting to average Lipschitzness.** Riazanov–Viola,
*Sampling Tools and the Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 15,
p.11: "Suppose f : {0, 1}^s → {0, 1}^b is an arbitrary depth-d decision forest. There exists a
100bd/µ-depth decision tree T querying symbols of {0, 1}^s such that for a leaf γ reached by the
uniform input to T, f|_γ is average-µ-Lipschitz with probability 0.99."

The output positions of `f` form any finite set of size `b`; the leaf reached by `x` is recorded
as the restriction fixing the bits queried on `x`'s path to their values in `x`.

**Formalization Note.** `µ > 0` is assumed because `100bd/µ` is undefined otherwise. The tree's
leaf labels are irrelevant (type `Unit`). -/
theorem lemma_15 : ∀ (s : ℕ) (ι : Type) [Fintype ι] (d : ℕ) (μ : ℝ), 0 < μ →
    ∀ f : Forest s ι, f.DepthLE d →
    ∃ T : QAlgorithms.DecisionTree (Fin s) Bool Unit,
      (∀ x, (T.queries x : ℝ) ≤ 100 * (Fintype.card ι : ℝ) * d / μ) ∧
      pr (unif (Fin s)) {x | AvgLipschitz f (pathRestriction T x) μ} ≥ 0.99 := by sorry

end SamplingAC0
