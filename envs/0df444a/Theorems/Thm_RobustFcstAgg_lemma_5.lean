-- Prove2me | Theorems.Thm_RobustFcstAgg_lemma_5
-- name    : RobustFcstAgg.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:57:32.486356+00:00
-- url     : https://prove2.me/theorems/031a44c9-6fc5-4602-bb6b-3ce8566f08ae
-- title:
--   Lemma 5 — symmetric coefficients lose nothing
-- statement:
--   For any $A\in\mathcal A^{\mathrm{lin}}_d$ with coefficients $\beta$ there is $A'\in\mathcal A^{\mathrm{lin}}_d$, implemented by a symmetric linear intersection rule $\hat R$, whose coefficient of $\mathrm{inter}(S)$ depends only on $|S|$, such that
--   $$\mathrm{error}(A')\le\mathrm{error}(A).$$
--
--   Symmetry is what turns the problem into one about a polynomial in $|T|$.
--
--   Differences from the source:
--   - reading: a symmetric linear intersection rule → coefficients of the form b(|S|); reason: "symmetric over set sizes", p.15, and β_{|S|}, p.16
--   - encoding: approximators A, [n], E[· | S_i], the law of (A, Y) and X_∅ = 0 → rules, whose error depends only on the a.s. class of the output; Fin n; integrals over the hidden signals; lintegrals in ℝ≥0∞; nonempty T only; reason: same instances; conditioning is by independence of the signals
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 5, p.15; proof p.27

import Mathlib
import Definitions.Def_RobustFcstAgg_linRule
import Definitions.Def_RobustFcstAgg_Rule_toRand
import Definitions.Def_RobustFcstAgg_RandRule_error

namespace RobustFcstAgg

/-- **Lemma 5.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 5, p.15 (proof p.27): for any `A ∈ A^lin_d` there is `A′ ∈ A^lin_d` implemented by an order-`d` symmetric
linear intersection rule with `error(A′) ≤ error(A)`.

**Formalization Note.** Symmetric coefficients depend on `S` only through `|S|`, as `β_{|S|}` on p.16. -/
theorem lemma_5 (n d : ℕ) (β : InterIndex n d → ℝ) :
    ∃ b : ℕ → ℝ, (linRule n d fun S => b S.1.card).toRand.error ≤ (linRule n d β).toRand.error := by sorry

end RobustFcstAgg
