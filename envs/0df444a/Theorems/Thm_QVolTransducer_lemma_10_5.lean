-- Prove2me | Theorems.Thm_QVolTransducer_lemma_10_5
-- name    : QVolTransducer.lemma_10_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:36.086204+00:00
-- url     : https://prove2.me/theorems/3e75794f-2bec-4991-8207-991068a2afc0
-- title:
--   Lemma 10.5 — anti-concentration of $\|x\|^2$ under $\pi_\beta$ (corrected: $K$ convex)
-- statement:
--   There is a universal constant $C>0$ such that for every integer $d\ge4$, every convex body $K\subseteq\mathbb R^d$ with $B_d\subseteq K$, every $\beta>0$ and all $0\le a<b$,
--
--   $$
--   \mathbb P_{x\sim\pi_\beta}\bigl[a\le\|x\|^2\le b\bigr]\ \le\ C\max\{d,\beta/\sqrt d\}\,(b-a).
--   $$
--
--   The bound gives the quantile gap needed to start the mean estimation of each cooling stage.
--
--   Differences from the source:
--   - correction: 4 ≤ d, B_d ⊆ K ⊆ ℝ^d, β > 0 (K not assumed convex) → K compact and convex with B_d ⊆ K; reason: the printed statement is false: for d = 4, β = η², K = B_4 ∪ {x : 1/η ≤ ‖x‖² ≤ 1/η + η}, the probability of a = 1/η ≤ ‖x‖² ≤ b = 1/η + η tends to 2/3 as η → 0 while C·max{4, η²/2}·η = 4Cη → 0; the proof (Lemma A.3) and Definition 5.1 assume a convex body (paper.md decision 7)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Lemma 10.5, p.71 (PDF p.73); proof Lemma A.3, p.80 (PDF p.82)

import Mathlib
import Definitions.Def_QVolTransducer_partitionFn

namespace QVolTransducer

/-- **Anti-concentration of `‖x‖²` under the Gibbs distribution** (Cornelissen, Apers, Gribling,
*Improved quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217
(version of November 3, 2026, sha256 40d7b52d…), Lemma 10.5, p.71 (PDF p.73), with the convexity
of `K` from its proof, Lemma A.3, p.80).

There is a universal constant `C > 0` such that for every `d ≥ 4`, every convex body `K ⊆ ℝ^d`
with `B_d ⊆ K`, every `β > 0` and all `0 ≤ a < b`:
`P_{x∼π_β}[a ≤ ‖x‖² ≤ b] ≤ C · max{d, β/√d} · (b − a)`.

**Formalization Note** The printed lemma assumes only `B_d ⊆ K ⊆ ℝ^d`; without convexity it is
false (for `d = 4`, `β = η²` and `K = B_4 ∪ {x : 1/η ≤ ‖x‖² ≤ 1/η + η}` the probability of the
shell tends to `2/3` while the bound `4Cη` tends to `0` as `η → 0`). Its proof (Lemma A.3) assumes
a convex `K`, as does Definition 5.1 of `π_β`; the statement adds that `K` is a convex body
(compact and convex). `C` is chosen before `d`, `K`, `β`, `a`, `b`. -/
theorem lemma_10_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (β a b : ℝ),
      4 ≤ d → IsCompact K → Convex ℝ K → Metric.closedBall 0 1 ⊆ K → 0 < β →
      0 ≤ a → a < b →
      gibbsProb K β {x | a ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 ≤ b} ≤
        C * max (d : ℝ) (β / Real.sqrt d) * (b - a) := by sorry

end QVolTransducer
