-- Prove2me | Theorems.Thm_RandomLPIPM_lemma_6_11
-- name    : RandomLPIPM.lemma_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:52.907606+00:00
-- url     : https://prove2.me/theorems/e05e0696-6625-4516-8ea8-d9fc48c18870
-- title:
--   Lemma 6.11 — continuity of the central-path gradient: $\le 2n|\log(\mu/\mu')|$
-- statement:
--   Let $A\in\mathbb R^{d\times n}$ have full row rank. For any $\mu,\mu'>0$ the central path of LP(A) satisfies
--   $$\Big\|\frac{d\log x_\mu}{d\log\mu}-\frac{d\log x_{\mu'}}{d\log\mu'}\Big\|_\infty\le 2n\,\Big|\log\frac{\mu}{\mu'}\Big|.$$
--
--   This deterministic modulus of continuity lets a bound proved on a grid of values of $\mu$ extend to a whole interval (Theorem 6.1).
--
--   Differences from the source:
--   - encoding: the logarithmic derivatives at μ and μ′ → ∃ g, g′ with HasDerivAt of t ↦ log x_{e^t, i} at log μ (resp. log μ′) for every i, and ‖g − g′‖_∞ ≤ 2n|log(μ/μ′)|; reason: asserts differentiability instead of using a junk-valued derivative
--   - encoding: x_μ the solution of the central path equations → x_μ the log-barrier minimizer; reason: equivalent by p.22
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 6.11, p.56

import Mathlib
import Definitions.Def_RandomLPIPM_xMu
import Definitions.Def_ColumnRandLP_Norms

open Matrix

namespace RandomLPIPM

/-- **Lemma 6.11 (Continuity of the Central-Path Gradient).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 6.11, p.56.

Let `A ∈ ℝ^{d×n}` have full row rank. For any `μ, μ′ > 0`, the central path of LP(A) satisfies
`‖d log x_μ / d log μ − d log x_μ′ / d log μ′‖_∞ ≤ 2n |log(μ/μ′)|`.

**Formalization Note.** The logarithmic derivatives are asserted to exist (`HasDerivAt` in
`t = log μ`, coordinatewise) and named `g`, `g′`; the statement does not assume differentiability. -/
theorem lemma_6_11 {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (hA : A.rank = d)
    (μ μ' : ℝ) (hμ : 0 < μ) (hμ' : 0 < μ') :
    ∃ g g' : Fin n → ℝ,
      (∀ i, HasDerivAt (fun t => Real.log (xMu A (Real.exp t) i)) (g i) (Real.log μ)) ∧
      (∀ i, HasDerivAt (fun t => Real.log (xMu A (Real.exp t) i)) (g' i) (Real.log μ')) ∧
      ColumnRandLP.supNorm (g - g') ≤ 2 * n * |Real.log (μ / μ')| := by sorry

end RandomLPIPM
