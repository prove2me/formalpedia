-- Prove2me | Theorems.Thm_RobustFcstAgg_Supplement_theorem_3
-- name    : RobustFcstAgg.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:42:00.495112+00:00
-- url     : https://prove2.me/theorems/57d229b2-3c79-44b4-95da-fa400fffd3d8
-- title:
--   Theorem 3 — under query complexity $d<n$ the minimum worst-case error is $1-d/n$
-- statement:
--   Let $d<n$. Over all approximators $A\in\mathcal A^{\mathrm{qry}}_d$, those implemented by DAG-elicitable randomized aggregation rules of query complexity at most $d$, the worst-case error has a minimum, and
--   $$
--   \min_{A\in\mathcal A^{\mathrm{qry}}_d}\mathrm{error}(A)=1-\frac dn .
--   $$
--   That is, some rule in the class has error exactly $1-d/n$, and no rule in the class has smaller error. Each additional query lowers the best achievable error by exactly $1/n$. The case $d=0$ is included: with no queries the best error is $1$.
--
--   **Formalization Note** The class is `IsQueryLE` (DAG-elicitable and at most $d$ queries for almost every context, jointly a.e.-measurable output; no order or agent bound). The error is the base `RandRule.error`, $\sup_{\mathcal D}L_{\mathcal D}(A)/\mathrm{Var}_{\mathcal D}(Y)$, in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: Condition 1 is imposed on every query elicitable with respect to any finite set of random variables (pp.14, 25) → Condition 1 is a clause of the class, on the variables scored on the eliciting DAG's edges; reason: the clause is weaker on the class, so the lower bound is at least as strong; the upper-bound rules satisfy it
--   - reading: a payment function π(r, R) exists (Definition 2) → one π for all instances D; reason: the principal does not know D (p.4); it matters only for the upper-bound class, which uses the quadratic score
--   - reading: the expectations E_D[π(r, R) | S_i] (Definition 2) and E[(A − Y)²] (Eq. (1)) → the payment is integrable on a.e. fibre for every report r, and in the class A^qry_d the randomized output is jointly a.e.-measurable in (z, signals); reason: the expectations the source writes presuppose both; the difference-query rules of Lemma 8 satisfy both
--   - encoding: approximators A, [n], E[· | S_i], X_∅ = 0 → rules, whose error depends only on the a.s. class of the output; Fin n; integrals over the hidden signals; lintegrals in ℝ≥0∞; nonempty T only; reason: same instances; conditioning is by independence of the signals
--   - encoding: min_{A∈A^qry_d} error(A) = 1 − d/n → IsLeast (qryErrorSet n d) (ENNReal.ofReal (1 − d/n)), real division; reason: the minimum is attained and is the least error; 1 − d/n ∈ (0, 1] under d < n, so ofReal loses nothing
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Theorem 3, p.11 (proof Appendix B, Lemmas 7 and 8, pp.23–25)

import Mathlib
import Definitions.Def_RobustFcstAgg_Supplement_qryErrorSet

namespace RobustFcstAgg.Supplement

/-- **Theorem 3.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*,
arXiv:2512.05271, Theorem 3, p.11 (proof App. B, Lemmas 7 and 8, pp.23–25): "Let `d < n`. Then
`min_{A ∈ A^qry_d} error(A) = 1 − d/n`."

**Formalization Note.** `min` is `IsLeast`: the value `1 − d/n` is attained by a rule of the class (Lemma 8) and no rule
of the class does better (Lemma 7). The class `A^qry_d` is `IsQueryLE` (randomized, a.e. DAG-elicitable, a.e. at most `d`
queries, jointly a.e.-measurable output; no order or agent bound). The error is the base `RandRule.error`, in `ℝ≥0∞`;
`1 − d/n ∈ (0, 1]` under `d < n`, so `ENNReal.ofReal` loses nothing. `d = 0` is included. -/
theorem theorem_3 (n d : ℕ) (hd : d < n) :
    IsLeast (qryErrorSet n d) (ENNReal.ofReal (1 - (d : ℝ) / n)) := by sorry

end RobustFcstAgg.Supplement
