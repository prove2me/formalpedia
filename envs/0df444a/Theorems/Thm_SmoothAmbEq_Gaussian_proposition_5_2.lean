-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_proposition_5_2
-- name    : SmoothAmbEq.Gaussian.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:58.994037+00:00
-- url     : https://prove2.me/theorems/41cbc25f-fc53-4bd5-bc8d-d6122b8fa0c0
-- title:
--   Proposition 5.2, p. 15 — condition (i) and the growth bound (5.6) imply admissibility
-- statement:
--   Let $\pi$ be a feedback strategy satisfying condition (i) of Definition 5.1, and suppose there is $C>0$ with
--   $$|\pi(t,x,\beta)|\le C\Big(1+|\beta|+\sqrt{\log(1+|x|)}\Big),\qquad(t,x,\beta)\in[0,T)\times\mathbb R^2.\qquad(5.6)$$
--   Then $\pi$ is admissible, i.e. it also satisfies the moment conditions (5.4)–(5.5).
--
--   The proposition shows that the admissible class is rich: every strategy of at most linear growth in $\beta$ and logarithmic growth in wealth with well-posed wealth dynamics belongs to it. It is how the paper shows that $\pi^*$ is admissible.
--
--   **Formalization Note** Admissibility is relative to the fixed probability space with Brownian motion $W$; condition (i) is read on the inside system for every drift value $z$ and every start (see the InsideSystem definition).
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 15, Proposition 5.2, (5.6)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SmoothAmbEq.Gaussian

/-- Proposition 5.2, p. 15. If a feedback strategy `π` satisfies condition (i) of
Definition 5.1 and the growth bound (5.6),
`|π(t, x, β)| ≤ C(1 + |β| + √(log(1 + |x|)))` on `[0, T) × ℝ²` for some `C > 0`,
then `π` is admissible. -/
theorem proposition_5_2 (M : Model) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (π : Strategy)
    (hi : AdmissibleI M P W π)
    (hgrowth : ∃ C > (0 : ℝ), ∀ t ∈ Ico 0 M.T, ∀ x β : ℝ,
      |π t x β| ≤ C * (1 + |β| + Real.sqrt (Real.log (1 + |x|)))) :
    Admissible M P W π := by sorry

end SmoothAmbEq.Gaussian
