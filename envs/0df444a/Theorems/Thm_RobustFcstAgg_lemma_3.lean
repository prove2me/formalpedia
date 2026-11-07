-- Prove2me | Theorems.Thm_RobustFcstAgg_lemma_3
-- name    : RobustFcstAgg.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:59:11.577289+00:00
-- url     : https://prove2.me/theorems/b6731961-f739-4b0e-a409-1f69e16abf7f
-- title:
--   Lemma 3 — worst-case Gaussian loss equals error for linear rules
-- statement:
--   For $n\ge1$,
--   $$\min_{A\in\mathcal A^{\mathrm{lin}}_d}\ \max_{\mathcal D_\lambda}L_{\mathcal D_\lambda}(A)=\min_{A\in\mathcal A^{\mathrm{lin}}_d}\mathrm{error}(A).$$
--   The formal statement gives the identity for each rule: $\mathrm{error}(A)=\max_{\mathcal D_\lambda}L_{\mathcal D_\lambda}(A)$ with the maximum attained, and the minimum of the error over linear rules exists.
--
--   This is what allows the minimax over Gaussian instances to be read as the error.
--
--   Differences from the source:
--   - generalization: equality of the two minima → for each β, error = the attained max over λ of the Gaussian loss, and the min of the error exists; reason: the proof on p.15 shows this pointwise form; minimizing it over β gives the printed identity
--   - encoding: n unrestricted → 1 ≤ n; reason: no information structure exists at n = 0, and the minimum is then undefined
--   - encoding: approximators A, [n], E[· | S_i], the law of (A, Y) and X_∅ = 0 → rules, whose error depends only on the a.s. class of the output; Fin n; integrals over the hidden signals; lintegrals in ℝ≥0∞; nonempty T only; reason: same instances; conditioning is by independence of the signals
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 3, p.15

import Mathlib
import Definitions.Def_RobustFcstAgg_linRule
import Definitions.Def_RobustFcstAgg_Rule_toRand
import Definitions.Def_RobustFcstAgg_RandRule_loss
import Definitions.Def_RobustFcstAgg_RandRule_error
import Definitions.Def_RobustFcstAgg_gaussInst
import Definitions.Def_RobustFcstAgg_linErrorSet

namespace RobustFcstAgg

/-- **Lemma 3.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 3, p.15: `min_{A ∈ A^lin_d} max_{D_λ} L_{D_λ}(A) = min_{A ∈ A^lin_d} error(A)`.

**Formalization Note.** The proof on p.15 shows `error(A) = max_{D_λ} L_{D_λ}(A)` for each `A`. That pointwise form is stated, with
attainment of the max, together with existence of the min; the printed identity follows by minimizing. -/
theorem lemma_3 (n d : ℕ) (hn : 1 ≤ n) :
    (∀ β : InterIndex n d → ℝ,
      IsGreatest (Set.range fun lam : stdSimplex ℝ (Subs n) => (linRule n d β).toRand.loss (gaussInst lam))
        (linRule n d β).toRand.error) ∧
    ∃ v, IsLeast (linErrorSet n d) v := by sorry

end RobustFcstAgg
