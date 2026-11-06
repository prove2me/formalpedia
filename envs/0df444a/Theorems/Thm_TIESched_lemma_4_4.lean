-- Prove2me | Theorems.Thm_TIESched_lemma_4_4
-- name    : TIESched.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:46:59.677397+00:00
-- url     : https://prove2.me/theorems/6d4e3fab-438e-4560-bfe7-653bf1126e0c
-- title:
--   Lemma 4.4 — limited decrease near the origin: $F(\rho)\ge\rho F'(0)-C_m\rho^2$
-- statement:
--   There is a constant $C_m\ge0$, depending only on $m$, such that for every star template (every choice of $L$ and $H$) and every feasible allocation family of interaction order at most $m-1$,
--   $$F(\rho)\ \ge\ \rho\,F'(0)-C_m\rho^2\qquad\text{for every }\rho\in[0,1].$$
--
--   A bounded-degree center load cannot fall quickly near the origin, while the optimum can (Lemma 4.2).
--
--   Differences from the source:
--   - encoding: F′(0) → deriv of the explicit polynomial F at 0; reason: same value
--   - encoding: vertices v_0, …, v_{m−1} and a bijection σ onto [m] → vertices Fin m with center 0 and σ : Equiv.Perm (Fin m); group labels are any pairwise disjoint sets of L natural numbers; reason: the same bijections and the same templates
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 4.4, p.16

import Mathlib
import Definitions.Def_TIESched_StarTemplate
import Definitions.Def_TIESched_interaction

set_option autoImplicit false

namespace TIESched

/-- **Lemma 4.4 (Limited decrease near the origin)** (Wang, Xu, Zhang, arXiv:2611.05142, Lemma 4.4,
p.16). There is a constant `C_m ≥ 0`, depending only on `m`, such that for every choice of `L` and
`H` (every star template) and every feasible allocation family of interaction order at most `m − 1`,
the expected center load satisfies `F(ρ) ≥ ρ F′(0) − C_m ρ²` for every `ρ ∈ [0, 1]`.

**Formalization Note.** The constant is quantified before the template and the family, so it
depends on `m` only. `F′(0)` is `deriv F 0`. -/
theorem lemma_4_4 (m : ℕ) [NeZero m] (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : StarTemplate m) (x : AllocFamily m), Feasible x →
      HasInteractionOrderLE x (m - 1) →
        ∀ ρ ∈ Set.Icc (0 : ℝ) 1, ρ * deriv (T.F x) 0 - C * ρ ^ 2 ≤ T.F x ρ := by sorry

end TIESched
