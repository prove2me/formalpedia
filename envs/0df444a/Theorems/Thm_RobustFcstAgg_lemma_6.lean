-- Prove2me | Theorems.Thm_RobustFcstAgg_lemma_6
-- name    : RobustFcstAgg.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:03:09.504867+00:00
-- url     : https://prove2.me/theorems/e0e348f8-bc48-42e0-a82f-fd64bfe1d922
-- title:
--   Lemma 6 — the polynomial characterization of the minimum error
-- statement:
--   For $n\ge1$ and every $d$, both minima exist and
--   $$\min_{A\in\mathcal A^{\mathrm{ord}}_d}\mathrm{error}(A)=\min_{p\in P_d,\ p(0)=1}\ \max_{t\in[n]}p(t)^2,\tag{4}$$
--   where $P_d$ is the set of polynomials of degree at most $d$.
--
--   The mechanism-design problem is thereby reduced to a one-variable problem in approximation theory on the integer points $1,\dots,n$.
--
--   Differences from the source:
--   - reading: Condition 1 is imposed on every query elicitable with respect to any finite set of random variables (pp.14, 25) → Condition 1 is a clause of the class, on the variables scored on the eliciting DAG's edges; reason: the clause is weaker on the class, so the lower bound is at least as strong; the upper-bound rules satisfy it
--   - reading: a payment function π(r, R) exists (Definition 2) → one π for all instances D; reason: the principal does not know D (p.4); it matters only for the upper-bound class, which uses the quadratic score
--   - reading: the expectations E_D[π(r, R) | S_i] (Definition 2) and E[(A − Y)²] (Eq. (1)) → the payment is integrable on a.e. fibre for every report r, and in the class A^ord_d the randomized output is jointly a.e.-measurable in (z, signals); reason: the expectations the source writes presuppose both; the linear intersection rules satisfy both
--   - encoding: n unrestricted → 1 ≤ n; reason: no information structure exists at n = 0, and the minimum is then undefined
--   - encoding: approximators A, [n], E[· | S_i], the law of (A, Y) and X_∅ = 0 → rules, whose error depends only on the a.s. class of the output; Fin n; integrals over the hidden signals; lintegrals in ℝ≥0∞; nonempty T only; reason: same instances; conditioning is by independence of the signals
--   - encoding: the minimum is a real number → ∃ v : ℝ, 0 ≤ v, with ENNReal.ofReal v the least element of the error set; reason: the error is valued in ℝ≥0∞; 0 ≤ v stops ofReal from hiding a negative value
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 6, Eq. (4), p.16

import Mathlib
import Definitions.Def_RobustFcstAgg_errorSet
import Definitions.Def_RobustFcstAgg_gridSet

namespace RobustFcstAgg

/-- **Lemma 6.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 6, Eq. (4), p.16: `min_{A ∈ A^ord_d} error(A) = min_{p ∈ P_d, p(0) = 1} max_{t ∈ [n]} p(t)²`.

**Formalization Note.** Both minima are attained. `1 ≤ n`: at `n = 0` neither side is defined. -/
theorem lemma_6 (n d : ℕ) (hn : 1 ≤ n) :
    ∃ v : ℝ, 0 ≤ v ∧ IsLeast (errorSet n d) (ENNReal.ofReal v) ∧ IsLeast (gridSet n d) v := by sorry

end RobustFcstAgg
