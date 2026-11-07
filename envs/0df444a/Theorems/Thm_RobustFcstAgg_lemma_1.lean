-- Prove2me | Theorems.Thm_RobustFcstAgg_lemma_1
-- name    : RobustFcstAgg.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:57:34.169621+00:00
-- url     : https://prove2.me/theorems/bfc16e25-59d6-4108-ba95-6d79ded308ee
-- title:
--   Lemma 1 — the output of a rule of order at most $d$ is a.s. a measurable function of $\mathcal Q_{\mathrm{inter}(d)}$
-- statement:
--   Let $P$ be a randomized DAG-elicitable aggregation rule with order complexity at most $d$. Then for every instance $\mathcal D$ and $P$-almost every realization $z$ there is a Borel-measurable function $g_{\mathcal D,z}$ with
--   $$f_z(\mathcal Q_z)=g_{\mathcal D,z}\bigl(\mathcal Q_{\mathrm{inter}(d)}\bigr)\quad\text{almost surely under }\mathcal D.$$
--
--   This is the structural heart of the lower bound: however a query is framed, on an eliciting DAG of order $d$ its answer carries no information beyond the intersection queries of order at most $d$.
--
--   **Formalization Note** The function $g$ may depend on $\mathcal D$ and on $z$, as on p.26, since queries depend on $\mathcal D$.
--
--   Differences from the source:
--   - generalization: A ∈ A^ord_d with agent-c(P) ≤ d and order-c(P) ≤ d → for a.e. z, the realized rule has an eliciting DAG with order ≤ d; no agent bound and no joint measurability of the output; reason: footnote 3, p.14 says the proof only requires bounded order; every rule of A^ord_d satisfies the hypothesis
--   - reading: Condition 1 is imposed on every query elicitable with respect to any finite set of random variables (pp.14, 25) → Condition 1 is a clause of the class, on the variables scored on the eliciting DAG's edges; reason: the clause is weaker on the class, so the lower bound is at least as strong; the upper-bound rules satisfy it
--   - reading: a payment function π(r, R) exists (Definition 2) → one π for all instances D; reason: the principal does not know D (p.4); it matters only for the upper-bound class, which uses the quadratic score
--   - reading: the expectations E_D[π(r, R) | S_i] (Definition 2) and E[(A − Y)²] (Eq. (1)) → the payment is integrable on a.e. fibre for every report r, and in the class A^ord_d the randomized output is jointly a.e.-measurable in (z, signals); reason: the expectations the source writes presuppose both; the linear intersection rules satisfy both
--   - encoding: approximators A, [n], E[· | S_i], the law of (A, Y) and X_∅ = 0 → rules, whose error depends only on the a.s. class of the output; Fin n; integrals over the hidden signals; lintegrals in ℝ≥0∞; nonempty T only; reason: same instances; conditioning is by independence of the signals
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 1, p.14; proof pp.25–26

import Mathlib
import Definitions.Def_RobustFcstAgg_RandRule
import Definitions.Def_RobustFcstAgg_Rule_output
import Definitions.Def_RobustFcstAgg_IsDAGElicits
import Definitions.Def_RobustFcstAgg_OrderLE
import Definitions.Def_RobustFcstAgg_InterIndex
import Definitions.Def_RobustFcstAgg_inter
import Definitions.Def_RobustFcstAgg_InfoStruct_jointLaw
open MeasureTheory

namespace RobustFcstAgg

/-- **Lemma 1.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 1, p.14 (proof pp.25–26): for every instance `D` and almost every realization `z ∼ P`, the
realized output `f_z(Q_z)` is almost surely a measurable function of `Q_inter(d)`.

**Formalization Note.** Only the order bound is assumed (footnote 3, p.14: the proof "only requires bounded order
complexity"). The function `g` may depend on `D` and `z`, as `g_{D,z}` on p.26 does: queries depend on `D`, so a uniform `g`
would be false. -/
theorem lemma_1 {n d : ℕ} (R : RandRule n)
    (hR : ∀ᵐ z ∂(R.P), ∃ out : (R.rule z).ι → Finset (Option (R.rule z).ι),
      IsDAGElicits (R.rule z).Q out ∧ OrderLE out d)
    (D : InfoStruct n) :
    ∀ᵐ z ∂(R.P), ∃ g : (InterIndex n d → ℝ) → ℝ, Measurable g ∧
      (R.rule z).output D =ᵐ[D.jointLaw] fun x => g fun S => inter S.1 x := by sorry

end RobustFcstAgg
