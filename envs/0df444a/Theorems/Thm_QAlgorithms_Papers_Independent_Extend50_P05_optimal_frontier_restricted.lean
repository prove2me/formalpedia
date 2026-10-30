-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_optimal_frontier_restricted
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.optimal_frontier_restricted
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:28:12.116996+00:00
-- url     : https://prove2.me/theorems/cbf9083b-846b-4250-a188-5fddc7fd134a
-- title:
--   Optimal qualities admit four-permutation realizations
-- statement:
--   Let $d\ge2$ and let $\mathcal R_d$ be the set of physically achievable pairs of depolarizing shrink parameters; let $\mathcal R_d^{\mathrm{restricted}}$ require a Choi matrix built from the four rank-$d$ partially transposed permutations. The full and restricted regions have exactly the same coordinatewise Pareto-optimal pairs. Furthermore, for all real $w,v\ge0$ with $w+v>0$,
--
--   $$
--   \exists(p,q)\in\mathcal R_d^{\mathrm{restricted}},\quad
--   \forall(r,s)\in\mathcal R_d,\quad wr+vs\le wp+vq.
--   $$
--
--   Pareto-optimal means that any achievable pair dominating $(p,q)$ in both coordinates equals $(p,q)$.
--
--   The result asserts the existence of a restricted realization of optimal qualities, without constraining every possible coefficient representation or declaring interior points optimal.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 13, Unnumbered main result: optimal cloners need only four permutations

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.2,13: Pareto-optimal quality pairs admit four-permutation realizations;
every nonzero nonnegative weighted support optimum has a restricted attaining channel. -/
theorem optimal_frontier_restricted (d : ℕ) (hd : 2 ≤ d) :
    (∀ p q : ℝ, IsParetoOptimal d p q ↔ IsRestrictedParetoOptimal d p q) ∧
    (∀ w v : ℝ, 0 ≤ w → 0 ≤ v → 0 < w + v →
      ∃ p q : ℝ, RestrictedAchievable d p q ∧
        ∀ r s : ℝ, CloningAchievable d r s → w * r + v * s ≤ w * p + v * q) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
