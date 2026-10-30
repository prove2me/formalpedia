-- Prove2me | Theorems.Thm_ThompsonTutorial_InfoRatio_sum_condMutualInfo_history_le_entropy
-- name    : ThompsonTutorial.InfoRatio.sum_condMutualInfo_history_le_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:13:54.546647+00:00
-- url     : https://prove2.me/theorems/c7ceb9fd-e024-407c-a65d-b546e5af49f8
-- title:
--   Information gains sum to at most the entropy: $\sum_{t=1}^T I(U;Z_t\mid H_{t-1})\le H(U)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, let $U:\Omega\to A$ be a random element and $(Z_t)_{t\ge1}$ a sequence of random elements $Z_t:\Omega\to B$, where $A$ and $B$ are standard Borel spaces, and let $H_t=(Z_1,\dots,Z_t)$. Then for every horizon $T\ge0$,
--   $$
--   \sum_{t=1}^T I\big(U;Z_t\mid H_{t-1}\big)\;\le\;H(U),
--   $$
--   in $[0,\infty]$, where $H(U)$ is the entropy of $U$ (possibly $+\infty$). With $U=x^*$ and $Z_t=(x_t,y_t)$ this is the tutorial's statement that the expected information gained about the optimal action, summed over periods, cannot exceed the entropy $H(x^*)$ of the prior on the optimal action. Together with the display following (8.8) it gives the regret bound (8.8).
--
--   **Formalization Note** Information in nats and in `ℝ≥0∞`.
--
--   Differences from the source:
--   - reading: I(x∗, (xt, yt)|Ht−1), printed with a comma → I(x*; (x_t, y_t) | H_{t−1}), the conditional mutual information of (8.7); reason: the same quantity, introduced as such on the preceding page
--   - generalization: the optimal action x* and the observations (x_t, y_t) of an algorithm in the model → any measurable U and any measurable process (Z_t) with values in standard Borel spaces; reason: the inequality holds for every process; the paper's case is U = x*, Z_t = (x_t, y_t) with X × Y standard Borel
--   - encoding: information and entropy in [0, ∞] → ℝ≥0∞, natural logarithm; reason: Lean convention; same values
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79), text following the display after (8.8)

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_history
import Definitions.Def_ThompsonTutorial_InfoRatio_entropy
open MeasureTheory
open scoped ENNReal

namespace ThompsonTutorial.InfoRatio

/-- **The information gains sum to at most the entropy: `∑_{t=1}^T I(U; Z_t | H_{t−1}) ≤ H(U)`.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79): "Intuitively, I(x∗, (xt, yt)|Ht−1) represents the
expected information gained about x∗, and the sum over periods cannot exceed the entropy H(x∗)."
The paper applies it with `U = x*` and `Z_t = (x_t, y_t)`.

For a probability measure `P`, a measurable random element `U` and a measurable process
`(Z_t)_{t ≥ 1}` in standard Borel nonempty spaces, and every `T`,
`∑_{t=1}^T I(U; Z_t | H_{t−1}) ≤ H(U)` with `H_t = (Z_1, …, Z_t)`.

**Formalization Note.** Inequality in `ℝ≥0∞`; nats; `H(U) = ⊤` when the law of `U` has a
non-atomic part. The printed `I(x∗, (xt, yt)|Ht−1)` (with a comma) is the conditional mutual
information `I(x∗; (xt, yt)|Ht−1)` of (8.7). Stated for an arbitrary random element and process. -/
theorem sum_condMutualInfo_history_le_entropy {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → A) (Z : ℕ → Ω → B)
    (hU : Measurable U) (hZ : ∀ t, Measurable (Z t)) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, condMutualInfo P U (Z t) (history Z (t - 1)) ≤ entropy P U := by sorry

end ThompsonTutorial.InfoRatio
