-- Prove2me | Theorems.Thm_TIESched_lemma_4_3
-- name    : TIESched.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:46:49.81959+00:00
-- url     : https://prove2.me/theorems/868a0653-2ade-4a6b-92e8-794dbc89d808
-- title:
--   Lemma 4.3 — polynomial representation: $F$ has degree $\le m-1$, $F(0)=0$, $0\le F(\rho)\le m\rho$
-- statement:
--   Let $x$ be a feasible fractional allocation family of interaction order at most $m-1$ and fix a star template. Then the expected center load $F$ is a polynomial in $\rho$ of degree at most $m-1$. Moreover $F(0)=0$ and
--   $$0\le F(\rho)\le m\rho\qquad\text{for every }\rho\in[0,1].$$
--
--   Bounded interaction order thus turns the center load into a low-degree polynomial with controlled range, the key restriction behind the lower bound.
--
--   Differences from the source:
--   - encoding: F is a polynomial of degree at most m − 1 → F = P.eval on all of ℝ for a real polynomial P with natDegree P ≤ m − 1; reason: F is the explicit finite sum defined for every real ρ; same statement
--   - encoding: vertices v_0, …, v_{m−1} and a bijection σ onto [m] → vertices Fin m with center 0 and σ : Equiv.Perm (Fin m); group labels are any pairwise disjoint sets of L natural numbers; reason: the same bijections and the same templates
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 4.3, p.15

import Mathlib
import Definitions.Def_TIESched_StarTemplate
import Definitions.Def_TIESched_interaction

set_option autoImplicit false

namespace TIESched

/-- **Lemma 4.3 (Polynomial representation)** (Wang, Xu, Zhang, arXiv:2611.05142, Lemma 4.3, p.15).
If the feasible fractional allocation family `x` has interaction order at most `m − 1`, then the
expected center load `F` of any star template is a polynomial of degree at most `m − 1`. Moreover
`F(0) = 0` and `0 ≤ F(ρ) ≤ mρ` for every `ρ ∈ [0, 1]`.

**Formalization Note.** `F` is the explicit finite sum `StarTemplate.F`, defined for every real `ρ`;
"is a polynomial of degree at most `m − 1`" is: `F = P.eval` on all of `ℝ` for some real polynomial
`P` with `natDegree P ≤ m − 1`. -/
theorem lemma_4_3 (m : ℕ) [NeZero m] (hm : 2 ≤ m) (T : StarTemplate m) (x : AllocFamily m)
    (hx : Feasible x) (hint : HasInteractionOrderLE x (m - 1)) :
    (∃ P : Polynomial ℝ, P.natDegree ≤ m - 1 ∧ ∀ ρ : ℝ, T.F x ρ = P.eval ρ) ∧ T.F x 0 = 0 ∧
      ∀ ρ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ T.F x ρ ∧ T.F x ρ ≤ (m : ℝ) * ρ := by sorry

end TIESched
