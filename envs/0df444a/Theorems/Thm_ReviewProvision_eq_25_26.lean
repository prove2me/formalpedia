-- Prove2me | Theorems.Thm_ReviewProvision_eq_25_26
-- name    : ReviewProvision.eq_25_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:57:34.741084+00:00
-- url     : https://prove2.me/theorems/e254d2ec-bdc6-4837-b714-e7f790904c58
-- title:
--   Eqs. (25)–(26), p.45 — derivatives of $\sigma^2_{F}$
-- statement:
--   Let $w\ge0$ coordinatewise, $T=\sum_l\eta w_l/(\eta+w_l)$. The partial derivatives of the closed form (12) in the coordinate $w_n$ are
--
--   $$
--   \frac{\partial\sigma_l^2}{\partial w_n}\bigg|_{l\ne n}=\frac{\eta^4}{(\tau+T)^2(\eta+w_n)^2(\eta+w_l)^2}>0,
--   \qquad
--   \frac{\partial\sigma_n^2}{\partial w_n}=\frac{[(\tau+T)(\eta+w_n)+\eta^2]^2}{(\tau+T)^2(\eta+w_n)^4}>0.
--   $$
--
--   More ratings in one cluster raise the variance of the customer evaluation in every cluster under FP.
--
--   **Formalization Note** The derivative is taken along the coordinate $n$ by `HasDerivAt`, and the pair of right sides is the function `dSigmaSqF`.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - encoding: partial derivatives ∂σ²_l/∂w_n → HasDerivAt of x ↦ σ²_{Fl}(w with w_n := x) at w_n; reason: the definition of a partial derivative; at w_n = 0 the closed form extends to a neighbourhood of 0 since its denominator is positive there
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), eqs. (25)–(26), p.45

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Eqs. (25)–(26)**, SSRN 3403322 (manuscript of 2021-05-24), p.45 (PDF 45): the partial derivative of
`σ²_{Fl}` in `w_n` is the right side of (25) for `l ≠ n` and of (26) for `l = n` (`dSigmaSqF`), and it is
positive.

**Formalization Note.** Stated by `HasDerivAt` of the closed form (12) along the coordinate `n`, at
every `w ≥ 0`. -/
theorem eq_25_26 (p : Params) {N : ℕ} (w : Fin N → ℝ) (hw : ∀ l, 0 ≤ w l) (l n : Fin N) :
    HasDerivAt (fun x => sigmaSqF p (Function.update w n x) l) (dSigmaSqF p w l n) (w n) ∧
    0 < dSigmaSqF p w l n := by sorry

end ReviewProvision
