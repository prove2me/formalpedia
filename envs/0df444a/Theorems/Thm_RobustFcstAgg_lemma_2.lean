-- Prove2me | Theorems.Thm_RobustFcstAgg_lemma_2
-- name    : RobustFcstAgg.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:01:26.968247+00:00
-- url     : https://prove2.me/theorems/19b2d13d-f71c-4491-b4bf-18937de6e744
-- title:
--   Lemma 2 — on Gaussian instances $\mathbb E[Y\mid\mathcal Q_{\mathrm{inter}(d)}]$ is linear, and the Gaussian lower bound
-- statement:
--   For any Gaussian instance $\mathcal D_\lambda$ there is a coefficient vector $\beta$ such that
--   $$\mathbb E_{\mathcal D_\lambda}\bigl[Y\mid\mathcal Q_{\mathrm{inter}(d)}\bigr]=\sum_{S:\,1\le|S|\le d}\beta_S\,\mathrm{inter}(S)\quad\text{almost surely.}$$
--   Consequently, for $n\ge1$ and any $A\in\mathcal A^{\mathrm{ord}}_d$,
--   $$\mathrm{error}(A)\ge\max_{\mathcal D_\lambda}\ \min_{A'\in\mathcal A^{\mathrm{lin}}_d}L_{\mathcal D_\lambda}(A').$$
--   The inner minimum and the outer maximum are both attained.
--
--   This reduces the general class to linear rules against each fixed Gaussian instance; $\lambda$ may have zero coordinates.
--
--   Differences from the source:
--   - reading: Condition 1 is imposed on every query elicitable with respect to any finite set of random variables (pp.14, 25) → Condition 1 is a clause of the class, on the variables scored on the eliciting DAG's edges; reason: the clause is weaker on the class, so the lower bound is at least as strong; the upper-bound rules satisfy it
--   - reading: a payment function π(r, R) exists (Definition 2) → one π for all instances D; reason: the principal does not know D (p.4); it matters only for the upper-bound class, which uses the quadratic score
--   - reading: the expectations E_D[π(r, R) | S_i] (Definition 2) and E[(A − Y)²] (Eq. (1)) → the payment is integrable on a.e. fibre for every report r, and in the class A^ord_d the randomized output is jointly a.e.-measurable in (z, signals); reason: the expectations the source writes presuppose both; the linear intersection rules satisfy both
--   - encoding: approximators A, [n], E[· | S_i], the law of (A, Y) and X_∅ = 0 → rules, whose error depends only on the a.s. class of the output; Fin n; integrals over the hidden signals; lintegrals in ℝ≥0∞; nonempty T only; reason: same instances; conditioning is by independence of the signals
--   - encoding: for any A ∈ A^ord_d, with no condition on n → the second clause assumes 1 ≤ n; reason: Δ is empty at n = 0 and the max is then undefined
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 2, p.14; proof p.26

import Mathlib
import Definitions.Def_RobustFcstAgg_gaussInst
import Definitions.Def_RobustFcstAgg_InfoStruct_jointLaw
import Definitions.Def_RobustFcstAgg_Y
import Definitions.Def_RobustFcstAgg_inter
import Definitions.Def_RobustFcstAgg_InterIndex
import Definitions.Def_RobustFcstAgg_linRule
import Definitions.Def_RobustFcstAgg_Rule_toRand
import Definitions.Def_RobustFcstAgg_RandRule_loss
import Definitions.Def_RobustFcstAgg_RandRule_error
import Definitions.Def_RobustFcstAgg_RandRule_IsOrderAgentLE
open MeasureTheory
open scoped ENNReal

namespace RobustFcstAgg

/-- **Lemma 2.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 2, p.14 (proof p.26): for any Gaussian instance `D_λ` there is `β` with
`E_{D_λ}[Y | Q_inter(d)] = Σ_S β_S inter(S)` a.s.; consequently, for any `A ∈ A^ord_d`,
`error(A) ≥ max_{D_λ} min_{A ∈ A^lin_d} L_{D_λ}(A)`.

**Formalization Note.** `w λ` is `min_{A ∈ A^lin_d} L_{D_λ}(A)`. The "min" and the "max" are attainment claims. `1 ≤ n` is needed
only for the second clause, since `Δ` is empty at `n = 0`; `λ` may have zeros. -/
theorem lemma_2 (n d : ℕ) :
    (∀ lam : stdSimplex ℝ (Subs n), ∃ β : InterIndex n d → ℝ,
      condExp (MeasurableSpace.comap (fun (x : Signals n) (S : InterIndex n d) => inter S.1 x) inferInstance)
          (gaussInst lam).jointLaw Y
        =ᵐ[(gaussInst lam).jointLaw] fun x => ∑ S, β S * inter S.1 x) ∧
    (1 ≤ n → ∃ w : stdSimplex ℝ (Subs n) → ℝ≥0∞,
      (∀ lam, IsLeast (Set.range fun β : InterIndex n d → ℝ => (linRule n d β).toRand.loss (gaussInst lam)) (w lam)) ∧
      ∃ v, IsGreatest (Set.range w) v ∧ ∀ R : RandRule n, R.IsOrderAgentLE d → v ≤ R.error) := by sorry

end RobustFcstAgg
