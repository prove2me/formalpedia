-- Prove2me | Theorems.Thm_TraceEstimation_ProjectionRank_chi_squared_tail
-- name    : TraceEstimation.ProjectionRank.chi_squared_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:14:18.376487+00:00
-- url     : https://prove2.me/theorems/6f826c38-20d6-4255-8825-fe5eb772cea4
-- title:
--   Lemma 5.3, proof — two-sided $\chi^2(k)$ tail bound $2\exp(-k\epsilon^2/6)$ for $0<\epsilon\le 1/2$
-- statement:
--   Let $k \ge 1$, let $g_1, \ldots, g_k$ be independent standard normal random variables, and let $X = \sum_{l=1}^k g_l^2$, so that $X \sim \chi^2(k)$. For every $\epsilon$ with $0 < \epsilon \le \tfrac12$,
--
--   $$\Pr\bigl(|X - k| \ge \epsilon k\bigr) \le 2\exp\!\left(-\frac{k\epsilon^2}{6}\right).$$
--
--   This is the $\chi^2$ concentration inequality that Avron and Toledo cite from Li, Hastie and Church (2007) and apply to $M G_M$ in the proof of Lemma 5.3.
--
--   **Formalization Note** Two corrections to the printed display. The paper prints $\Pr(|X-k| \le \epsilon k) \le 2\exp(-k\epsilon^2/6)$; the inner $\le$ is a misprint for $\ge$, as the next display, which applies the bound, shows. The paper gives no range for $\epsilon$, and the bound is false for $\epsilon = 1$ and large $k$: the upper tail $\Pr(X \ge 2k)$ decays like $e^{-k(1-\ln 2)/2} \approx e^{-0.153k}$, slower than $e^{-k/6}$. The statement is therefore restricted to $0 < \epsilon \le 1/2$, which contains the only value the proof uses, $\epsilon = 1/(2\,\mathrm{rank}(A))$. The $\chi^2(k)$ variable is modelled as the sum of squares on the product space `Fin k → ℝ` with `Measure.pi (fun _ => gaussianReal 0 1)`, and the probability is `Measure.real`.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:9, proof of Lemma 5.3, tail bound cited from [Li et al. 2007]

import Mathlib

namespace TraceEstimation.ProjectionRank

open MeasureTheory ProbabilityTheory

/-- The `χ²` tail bound Avron–Toledo cite from [Li et al. 2007] (Lemma 5.3, proof, p. 8:9):
if `X = ∑_{l=1}^k g_l²` with `g_1, …, g_k` i.i.d. standard normal (`X ∼ χ²(k)`), `k ≥ 1`,
and `0 < ε ≤ 1/2`, then `Pr(|X - k| ≥ ε k) ≤ 2 exp(-k ε² / 6)`.

Two corrections to the printed display `Pr(|X - k| ≤ ε k) ≤ 2 exp(-k ε²/6)`: the `≤` inside
the probability is a misprint for `≥` (the next display, which applies the bound, has `≥`);
and the page gives no range for `ε`, while the bound fails for `ε = 1` and large `k` (the
upper tail decays like `exp(-k (1 - ln 2)/2)`, slower than `exp(-k/6)`). It holds for
`0 < ε ≤ 1/2`, which covers the only value the proof uses, `ε = 1/(2 rank(A))`. -/
theorem chi_squared_tail (k : ℕ) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1).real
        {g | ε * k ≤ |∑ l, g l ^ 2 - k|} ≤ 2 * Real.exp (-(k * ε ^ 2 / 6)) := by sorry

end TraceEstimation.ProjectionRank
