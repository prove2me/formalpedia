-- Prove2me | Theorems.Thm_ThompsonTutorial_InfoRatio_sum_condMutualInfo_history_eq_mutualInfo
-- name    : ThompsonTutorial.InfoRatio.sum_condMutualInfo_history_eq_mutualInfo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:12:58.877664+00:00
-- url     : https://prove2.me/theorems/7347b58f-2abc-4d0e-a82d-547f705727af
-- title:
--   Chain rule of mutual information: $\sum_{t=1}^T I(U;Z_t\mid H_{t-1})=I(U;H_T)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, let $U:\Omega\to A$ be a random element and $(Z_t)_{t\ge1}$ a sequence of random elements $Z_t:\Omega\to B$, where $A$ and $B$ are standard Borel spaces. Let $H_t=(Z_1,\dots,Z_t)$ be the history. Then for every horizon $T\ge0$,
--   $$
--   \sum_{t=1}^T I\big(U;Z_t\mid H_{t-1}\big)\;=\;I(U;H_T),
--   $$
--   as an identity in $[0,\infty]$. This is the chain rule of mutual information, which the tutorial invokes (citing Russo and Van Roy, 2016) to show that the information gains $I(x^*;(x_t,y_t)\mid H_{t-1})$ add up to the information the whole history carries about the optimal action; it is applied with $U=x^*$ and $Z_t=(x_t,y_t)$.
--
--   **Formalization Note** Information in nats and in `ℝ≥0∞`; $H_0$ is the empty history, so the case $T=0$ reads $0=I(U;H_0)=0$.
--
--   Differences from the source:
--   - reading: "formally established … via the chain rule of mutual information" (the identity is named, not displayed) → ∑_{t=1}^T I(U; Z_t | H_{t−1}) = I(U; H_T); reason: this is the chain rule in the form the argument needs
--   - generalization: the optimal action x* and the observations (x_t, y_t) of an algorithm in the model → any measurable U and any measurable process (Z_t) with values in standard Borel spaces; reason: the identity holds for every process; the paper's case is U = x*, Z_t = (x_t, y_t) with X × Y standard Borel
--   - encoding: mutual information in [0, ∞] → ℝ≥0∞, natural logarithm; reason: Lean convention; same values
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79), text following the display after (8.8): "via the chain rule of mutual information"

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_history
open MeasureTheory
open scoped ENNReal

namespace ThompsonTutorial.InfoRatio

/-- **Chain rule of mutual information along a history: `∑_{t=1}^T I(U; Z_t | H_{t−1}) = I(U; H_T)`.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 76 (PDF p. 79): "Applying this relation, which is formally
established in (Russo and Van Roy, 2016) via the chain rule of mutual information, we obtain
(8.8)." The paper applies it with `U = x*` and `Z_t = (x_t, y_t)`, so that `H_t` is the history.

For a probability measure `P`, a measurable random element `U` and a measurable process
`(Z_t)_{t ≥ 1}` in standard Borel nonempty spaces, and every `T`,
`∑_{t=1}^T I(U; Z_t | H_{t−1}) = I(U; H_T)` with `H_t = (Z_1, …, Z_t)`.

**Formalization Note.** Equality in `ℝ≥0∞` (both sides may be `⊤`); nats. Stated for an arbitrary
random element and process, of which the paper's `x*` and `((x_t, y_t))_t` are an instance. `Z 0`
is not used; `t − 1` is evaluated only for `t ≥ 1`. -/
theorem sum_condMutualInfo_history_eq_mutualInfo {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → A) (Z : ℕ → Ω → B)
    (hU : Measurable U) (hZ : ∀ t, Measurable (Z t)) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, condMutualInfo P U (Z t) (history Z (t - 1)) =
      mutualInfo P U (history Z T) := by sorry

end ThompsonTutorial.InfoRatio
