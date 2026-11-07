-- Prove2me | Theorems.Thm_RobustFcstAgg_eq_3
-- name    : RobustFcstAgg.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:55:17.957304+00:00
-- url     : https://prove2.me/theorems/1a9e6d37-62a4-4564-b69e-101a5f1a9868
-- title:
--   Eq. (3) — the normalized loss of a linear rule is $\sum_T\lambda_T g_T(\beta)^2$
-- statement:
--   For every instance $\mathcal D$ and every $\beta$, the linear intersection rule $A=\sum_S\beta_S\,\mathrm{inter}(S)$ satisfies
--   $$\frac{\mathbb E(Y-A)^2}{\sum_T\mathrm{Var}_{\mathcal D}(X_T)}=\sum_T\lambda_T\,g_T(\beta)^2,\qquad \lambda_T=\frac{\mathrm{Var}_{\mathcal D}(X_T)}{\sum_T\mathrm{Var}_{\mathcal D}(X_T)}.$$
--
--   So the normalized loss of a linear rule depends on the instance only through its variance profile, which is what lets Gaussian instances stand in for all instances.
--
--   Differences from the source:
--   - encoding: a chain of equalities of real numbers → the first and last terms only, with the loss in ℝ≥0∞ and the right side through ENNReal.ofReal; reason: same value; the loss is finite and the right side is nonnegative
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Eq. (3), p.15

import Mathlib
import Definitions.Def_RobustFcstAgg_linRule
import Definitions.Def_RobustFcstAgg_Rule_toRand
import Definitions.Def_RobustFcstAgg_RandRule_loss
import Definitions.Def_RobustFcstAgg_InfoStruct_varY
import Definitions.Def_RobustFcstAgg_gCoeff
open MeasureTheory

namespace RobustFcstAgg

/-- **Eq. (3).** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Eq. (3), p.15: the normalized loss of a linear intersection rule is `Σ_T λ_T g_T(β)²`, with
`λ_T := Var_D(X_T) / Σ_T Var_D(X_T)`. -/
theorem eq_3 {n d : ℕ} (β : InterIndex n d → ℝ) (D : InfoStruct n) :
    (linRule n d β).toRand.loss D / ENNReal.ofReal D.varY =
      ENNReal.ofReal (∑ T, (D.varT T / D.varY) * (gCoeff β T) ^ 2) := by sorry

end RobustFcstAgg
