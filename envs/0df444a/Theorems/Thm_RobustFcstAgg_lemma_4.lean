-- Prove2me | Theorems.Thm_RobustFcstAgg_lemma_4
-- name    : RobustFcstAgg.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:00:53.877789+00:00
-- url     : https://prove2.me/theorems/95b855bb-4cd8-4283-afcf-81b7f118cdbb
-- title:
--   Lemma 4 — $\mathrm{error}(A)\ge\min_{A\in\mathcal A^{\mathrm{lin}}_d}\mathrm{error}(A)$
-- statement:
--   For $n\ge1$, the minimum of the error over deterministic linear intersection rules exists, and every $A\in\mathcal A^{\mathrm{ord}}_d$ satisfies
--   $$\mathrm{error}(A)\ge\min_{A'\in\mathcal A^{\mathrm{lin}}_d}\mathrm{error}(A').$$
--
--   This is the lower-bound half of the reduction to linear rules.
--
--   Differences from the source:
--   - reading: Condition 1 is imposed on every query elicitable with respect to any finite set of random variables (pp.14, 25) → Condition 1 is a clause of the class, on the variables scored on the eliciting DAG's edges; reason: the clause is weaker on the class, so the lower bound is at least as strong; the upper-bound rules satisfy it
--   - reading: a payment function π(r, R) exists (Definition 2) → one π for all instances D; reason: the principal does not know D (p.4); it matters only for the upper-bound class, which uses the quadratic score
--   - reading: the expectations E_D[π(r, R) | S_i] (Definition 2) and E[(A − Y)²] (Eq. (1)) → the payment is integrable on a.e. fibre for every report r, and in the class A^ord_d the randomized output is jointly a.e.-measurable in (z, signals); reason: the expectations the source writes presuppose both; the linear intersection rules satisfy both
--   - encoding: n unrestricted → 1 ≤ n; reason: no information structure exists at n = 0, and the minimum is then undefined
--   - encoding: approximators A, [n], E[· | S_i], the law of (A, Y) and X_∅ = 0 → rules, whose error depends only on the a.s. class of the output; Fin n; integrals over the hidden signals; lintegrals in ℝ≥0∞; nonempty T only; reason: same instances; conditioning is by independence of the signals
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 4, p.15; proof p.27

import Mathlib
import Definitions.Def_RobustFcstAgg_linErrorSet
import Definitions.Def_RobustFcstAgg_RandRule_IsOrderAgentLE
import Definitions.Def_RobustFcstAgg_RandRule_error

namespace RobustFcstAgg

/-- **Lemma 4.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 4, p.15 (proof p.27): for `A ∈ A^ord_d`, `error(A) ≥ min_{A ∈ A^lin_d} error(A)`.

**Formalization Note.** `1 ≤ n`: no information structure exists at `n = 0`. The min is an attainment claim. -/
theorem lemma_4 (n d : ℕ) (hn : 1 ≤ n) :
    ∃ v, IsLeast (linErrorSet n d) v ∧ ∀ R : RandRule n, R.IsOrderAgentLE d → v ≤ R.error := by sorry

end RobustFcstAgg
