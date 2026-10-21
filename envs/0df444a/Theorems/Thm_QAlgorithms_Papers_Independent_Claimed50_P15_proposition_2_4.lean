-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_proposition_2_4
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.proposition_2_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:41:55.843987+00:00
-- url     : https://prove2.me/theorems/b998c077-e9af-43d3-a5fc-de94e0c71f1f
-- title:
--   Proposition 2.4
-- statement:
--   Under Assumption LD, let $P_t$ be finite nonzero measures on possibly varying spaces, $X_t$ measurable and real, and positive $w_t\to\infty$ along an arbitrary unbounded positive real index set. Suppose that the finite continuous limiting scaled log moment function $e$ is defined on $[a,b]$ with $a<0<b$, that $e(0)\le0$, and that $e$ is differentiable at zero. For every $\delta>0$, there are $\gamma>0$ and a real threshold $t_0$ such that, for every index $t\ge t_0$,
--
--   $$P_t\bigl(|w_t^{-1}X_t-e'(0)|\ge\delta\bigr)\le e^{-\gamma w_t}.$$
--
--   The constants precede the final index quantifier, and no probability normalization is assumed.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 8, Proposition 2.4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 2.4, arXiv:1109.3804v2, PDF p.8.
No probability normalization is imposed; gamma and t0 precede every later t. -/
theorem proposition_2_4 (F : LDFamily) (a b : ℝ) (ha : a < 0) (hb : 0 < b)
    (e : ℝ → ℝ) (hLD : HasLD F a b e) (he : e 0 ≤ 0)
    (hdiff : DifferentiableAt ℝ e 0) :
    ∀ delta : ℝ, 0 < delta → ∃ gamma : ℝ, 0 < gamma ∧ ∃ t0 : ℝ,
      ∀ t : F.index, t0 ≤ t.val →
        (F.experiment t).measure {x | delta ≤
          |(F.weight t)⁻¹ * (F.experiment t).observable x - deriv e 0|} ≤
            ENNReal.ofReal (Real.exp (-gamma * F.weight t)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
