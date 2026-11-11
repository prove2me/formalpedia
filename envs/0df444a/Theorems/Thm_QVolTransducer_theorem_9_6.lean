-- Prove2me | Theorems.Thm_QVolTransducer_theorem_9_6
-- name    : QVolTransducer.theorem_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:08.814913+00:00
-- url     : https://prove2.me/theorems/051f99fd-557a-46b3-aaf4-0237c33170d6
-- title:
--   Theorem 9.6 — two-sided bounds on the mean and variance of $\|x\|^2$ under $\pi_\beta$
-- statement:
--   There is a universal constant $c>0$ such that for all $d\ge1$, $R\ge1$, every convex $K$ with $B_d\subseteq K\subseteq RB_d$, $H(x)=\|x\|^2$ and every $\beta\ge0$:
--
--   $$
--   c\,\min\Bigl\{\frac d\beta,1\Bigr\}\ \le\ \mathbb E_{x\sim\pi_\beta}[H(x)]\ \le\ \min\Bigl\{\frac d{2\beta},R^2\Bigr\},
--   $$
--
--   $$
--   c\,\min\Bigl\{\frac d{\beta^2},\frac1{d^2}\Bigr\}\ \le\ \mathrm{Var}_{x\sim\pi_\beta}[H(x)]\ \le\ \min\Bigl\{\frac d{\beta^2},\frac{2R^2}\beta,\frac{R^4}4\Bigr\}.
--   $$
--
--   At $\beta=0$ every quotient with $\beta$ in the denominator is $+\infty$, so each minimum is its remaining term. These bounds control the overlap of consecutive Gibbs states and the variance of the cooling estimators.
--
--   Differences from the source:
--   - encoding: Ω(min{d/β, 1}) ∋ E and Ω(min{d/β², 1/d²}) ∋ Var → c·min{…} ≤ E and c·min{…} ≤ Var with one universal c > 0 chosen before all parameters; reason: paper.md decision 12
--   - encoding: min{…} with terms d/β, d/(2β), d/β², 2R²/β at β = 0 → separate clauses for β > 0 and β = 0, where these terms are +∞; reason: Lean's division by zero returns 0
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 9.6, p.56 (PDF p.58); proof in Appendix A

import Mathlib
import Definitions.Def_QVolTransducer_partitionFn

namespace QVolTransducer

/-- **Mean and variance of `‖x‖²` under the Gibbs distribution** (Cornelissen, Apers, Gribling,
*Improved quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217
(version of November 3, 2026, sha256 40d7b52d…), Theorem 9.6, p.56 (PDF p.58)).

There is a universal constant `c > 0` such that for every `d ≥ 1`, `R ≥ 1`, convex
`B_d ⊆ K ⊆ RB_d`, `H(x) = ‖x‖²` and every `β ≥ 0`:
`c·min{d/β, 1} ≤ E_{x∼π_β}[H(x)] ≤ min{d/(2β), R²}` and
`c·min{d/β², 1/d²} ≤ Var_{x∼π_β}[H(x)] ≤ min{d/β², 2R²/β, R⁴/4}`.

**Formalization Note** The paper's `Ω(·)` are lower bounds with one universal constant `c`, chosen
before all parameters. At `β = 0` the quotients `d/β`, `d/(2β)`, `d/β²`, `2R²/β` are `+∞`, so each
minimum is its remaining term; the statement splits the cases `β > 0` and `β = 0` accordingly. -/
theorem theorem_9_6 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (R : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))) (β : ℝ),
      1 ≤ d → 1 ≤ R → Convex ℝ K → Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
      0 ≤ β →
      gibbsMean K β (fun x => ‖x‖ ^ 2) ≤ R ^ 2 ∧
      (0 < β → gibbsMean K β (fun x => ‖x‖ ^ 2) ≤ d / (2 * β)) ∧
      gibbsVar K β (fun x => ‖x‖ ^ 2) ≤ R ^ 4 / 4 ∧
      (0 < β → gibbsVar K β (fun x => ‖x‖ ^ 2) ≤ d / β ^ 2 ∧
        gibbsVar K β (fun x => ‖x‖ ^ 2) ≤ 2 * R ^ 2 / β) ∧
      (0 < β → c * min (d / β) 1 ≤ gibbsMean K β (fun x => ‖x‖ ^ 2)) ∧
      (β = 0 → c ≤ gibbsMean K β (fun x => ‖x‖ ^ 2)) ∧
      (0 < β → c * min (d / β ^ 2) (1 / (d : ℝ) ^ 2) ≤ gibbsVar K β (fun x => ‖x‖ ^ 2)) ∧
      (β = 0 → c * (1 / (d : ℝ) ^ 2) ≤ gibbsVar K β (fun x => ‖x‖ ^ 2)) := by sorry

end QVolTransducer
