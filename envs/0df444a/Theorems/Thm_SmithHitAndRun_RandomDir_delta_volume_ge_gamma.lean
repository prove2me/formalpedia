-- Prove2me | Theorems.Thm_SmithHitAndRun_RandomDir_delta_volume_ge_gamma
-- name    : SmithHitAndRun.RandomDir.delta_volume_ge_gamma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:37:48.016984+00:00
-- url     : https://prove2.me/theorems/3da4eb6b-cbb8-47b0-8b9d-31cae3e37c52
-- title:
--   Proof of Theorem 3 — $\delta V(S)\ge\gamma/(n2^{n-1})$
-- statement:
--   Let $n\ge1$ and let $S\subseteq\mathbb R^n$ be open, bounded and nonempty, with content $V(S)$ and diameter $d$. Let $\delta=2/(d\,S_n(d))$ and let $\gamma$ be the ratio of $V(S)$ to the content of the smallest ball containing $S$. Then
--   $$\delta\,V(S)\ \ge\ \frac{\gamma}{n\,2^{n-1}}.$$
--
--   This converts the constant $\delta\varphi(C)=\delta V(S)$ of Doob's bound into the geometric constant $\gamma/(n2^{n-1})$ of Theorem 3.
--
--   **Formalization Note** The paper argues via $\delta=1/(n2^{n-1}V_n(d/2))$ and the claim that $V_n(d/2)$ is the volume of a circumscribed sphere around $S$. That claim is not true in general (an equilateral triangle of side $d$ has smallest enclosing radius $d/\sqrt3>d/2$); what holds, and suffices, is $V_n(d/2)\le V_n(R^\star)$, i.e. the inequality stated here.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1304, Proof of Theorem 3

import Mathlib
import Definitions.Def_SmithHitAndRun_RandomDir_RateConstants

open MeasureTheory

namespace SmithHitAndRun.RandomDir

/-- Smith 1984, p. 1304, end of the proof of Theorem 3: for an open bounded nonempty region
`S ⊆ ℝⁿ` with diameter `d`, `δ V(S) ≥ γ / (n 2^{n−1})`, where `δ = 2 / (d S_n(d))` and `γ` is the
ratio of the content of `S` to the content of the smallest ball containing `S`. -/
theorem delta_volume_ge_gamma {n : ℕ} (hn : 1 ≤ n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSo : IsOpen S) (hSb : Bornology.IsBounded S)
    (hSne : S.Nonempty) :
    gammaRatio S / ((n : ℝ) * 2 ^ (n - 1)) ≤ deltaConst S * (volume S).toReal := by sorry

end SmithHitAndRun.RandomDir
