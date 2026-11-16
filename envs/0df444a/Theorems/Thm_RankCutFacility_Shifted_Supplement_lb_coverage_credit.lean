-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_lb_coverage_credit
-- name    : RankCutFacility.Shifted.Supplement.lb_coverage_credit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:23:00.044565+00:00
-- url     : https://prove2.me/theorems/3fbd87c9-d28d-4264-88bc-bf450fa5d3ca
-- title:
--   Lemma 6.4 — Coverage credit $\mathbb E[C]\le\tfrac32\mathbb E[K]$
-- statement:
--   On the instance of Section 6.1 with $N\ge2$, draw the $N$ demand points independently and uniformly from $X$ and serve them in the drawn order. A round with demand $x_i$ is covered if, after the openings of that round, some open facility $y_I$ has $i\in I$. Let $C$ be the number of covered rounds and $K$ the number of distinct facilities opened.
--
--   **Lemma 6.4.** For every randomized online algorithm (which may know the metric, costs, horizon and demand distribution and may open several facilities in a round),
--
--   $$\mathbb E[C]\le\frac32\,\mathbb E[K],$$
--
--   with expectations over the i.i.d. demand points and the algorithm's internal randomness.
--
--   This bounds the connection savings one opening can buy and is the core of the $3-o(1)$ lower bound.
--
--   Differences from the source:
--   - encoding: a randomized online algorithm (knowing the metric, costs, horizon and demand distribution, possibly opening several facilities per round) → a probability mass function over deterministic online algorithms, each a map from the revealed request prefix to the finite set of candidates opened in that round, independent of the demand randomness; reason: on a fixed finite instance with fixed horizon only finitely many deterministic behaviours exist, so every randomized algorithm is such a mixture; the public data are fixed before the algorithm is chosen
--   - encoding: N independent uniform draws from X → the uniform average over all maps Fin N → Fin m; reason: this is the product uniform law on a finite set
--   - encoding: C and K as random counts → coveredRounds and openedCount, natural numbers cast to [0, ∞]; reason: the expectations are finite averages of these counts
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Lemma 6.4, printed p. 20 (PDF p. 22)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Online

noncomputable section
open scoped ENNReal

namespace RankCutFacility.Shifted.Supplement

/-- Lemma 6.4 (PDF p. 22, printed p. 20): in the i.i.d. experiment on the instance of
Section 6.1, every randomized online algorithm has `E[C] ≤ (3/2) E[K]`. -/
theorem lb_coverage_credit (N : ℕ) (hN : 2 ≤ N) (ρ : PMF (OnlineAlg (LBFac N) (LBPoint N))) :
    iidExpected ρ (fun A w => (coveredRounds A w : ℝ≥0∞)) ≤
      (3 / 2 : ℝ≥0∞) * iidExpected ρ (fun A w => (openedCount A w : ℝ≥0∞)) := by sorry

end RankCutFacility.Shifted.Supplement
