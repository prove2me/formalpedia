-- Prove2me | Theorems.Thm_ProbMetricStab_MixedInt_lemma_3_5_b
-- name    : ProbMetricStab.MixedInt.lemma_3_5_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:25.30575+00:00
-- url     : https://prove2.me/theorems/2ab5c452-bb12-49c9-b54a-68e699f2cb33
-- title:
--   Lemma 3.5, last assertion, p. 15 — Φ finite and lsc on 𝒯, and |Φ(t) − Φ(t̃)| ≤ α‖t − t̃‖ + β
-- statement:
--   Let $\Phi$ be the mixed-integer value function (10), with recourse data satisfying (B1) (rational $W$, $\bar W$) and (B3) (dual feasibility), and let $\mathcal T$ be its feasibility set. Then
--
--   1. $\Phi(t)$ is finite for every $t\in\mathcal T$;
--   2. $\Phi$ is lower semicontinuous on $\mathcal T$;
--   3. there are constants $\alpha>0$ and $\beta>0$ such that for all $t,\tilde t\in\mathcal T$
--   $$
--   |\Phi(t)-\Phi(\tilde t)|\le\alpha\|t-\tilde t\|+\beta .
--   $$
--
--   The last estimate, a Lipschitz bound up to an additive constant, is what gives the integrand $f_0$ of (9) linear growth in $(\xi,x)$ and so puts every measure with a finite first moment into the domain of the minimal information distance.
--
--   **Formalization Note** Item 1 is the remark made on p. 14 just before the lemma ("(B2) and (B3) imply that $\Phi(t)$ is finite for all $t\in\mathcal T$"); it is stated here because the estimate compares real values. The lemma also calls $\Phi$ "piecewise polyhedral" on $\mathcal T$; the paper does not define the term, and that clause is not formalized. Lower semicontinuity is relative to $\mathcal T$, for the extended-real function $\Phi$. (B2) is omitted, as in part (i)–(ii).
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 15, Lemma 3.5, last assertion ("Furthermore, …"); p. 14, remark after (B3)

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_Setting
open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt
theorem lemma_3_5_b {r mh mb : ℕ} (R : Recourse r mh mb) (hB1 : R.B1) (hB3 : R.B3) :
    (∀ t ∈ R.Tset, R.Phi t ≠ ⊤ ∧ R.Phi t ≠ ⊥) ∧
    LowerSemicontinuousOn R.Phi R.Tset ∧
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ t ∈ R.Tset, ∀ t' ∈ R.Tset,
      |(R.Phi t).toReal - (R.Phi t').toReal| ≤ α * ‖t - t'‖ + β := by sorry
end ProbMetricStab.MixedInt
