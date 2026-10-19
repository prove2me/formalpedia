-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_two_moment_discrete_optimum
-- name    : QAlgorithms.Papers.Independent.Information100.P19.two_moment_discrete_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:53:55.424104+00:00
-- url     : https://prove2.me/theorems/5d5fb410-8174-467d-9ce6-d5cecdf606a3
-- title:
--   Theorem 5.5
-- statement:
--   For nonnegative data $r_1,r_2$ with $r_1\le1$, the discrete unit-atom problem is feasible exactly when $0<r_2\le r_1^2\le1$ or both data vanish. In the positive case put $n=\lceil r_1^2/r_2\rceil$, $m=n-1$, and $\Delta=\sqrt{nr_2-r_1^2}$. The minimum is attained with exactly $n$ positive entries and
--   $$\alpha(r_1,r_2)=\frac{\sqrt{m^2r_1+m^{3/2}\Delta}+\sqrt{r_1-\sqrt m\Delta}}{\sqrt n}.$$
--   If $r_1^2/r_2$ is integral, $\Delta=0$ and the value is $r_1^{3/2}/\sqrt{r_2}$. At $(0,0)$ the value is zero; infeasible data have value $+\infty$.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 31, Theorem 5.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Theorem 5.5; arXiv:2609.29471v1, PDF pp.31, 52, 53. -/
theorem two_moment_discrete_optimum (r1 r2 : ℝ) (h1 : 0≤r1) (h2 : 0≤r2) (hbound : r1≤1) :
    (alpha ![r1,r2] < ∞ ↔ (0<r2 ∧ r2≤r1^2 ∧ r1^2≤1) ∨ (r1=0 ∧ r2=0)) ∧
    ((0<r2 ∧ r2≤r1^2) →
      let n : ℕ := Nat.ceil (r1^2/r2)
      let m : ℝ := (n-1 : ℕ)
      let delta := Real.sqrt ((n:ℝ)*r2-r1^2)
      alpha ![r1,r2] = ENNReal.ofReal
        ((Real.sqrt (m^2*r1+m*Real.sqrt m*delta) + Real.sqrt (r1-Real.sqrt m*delta)) /
          Real.sqrt n) ∧
      (∃ s : Fin n → ℝ, discreteFeasible ![r1,r2] s ∧ (∀ i, 0<s i) ∧
        alpha ![r1,r2] = ENNReal.ofReal (∑ i, s i)) ∧
      ((∃ k : ℕ, r1^2/r2 = (k:ℝ)) → delta=0 ∧
        alpha ![r1,r2] = ENNReal.ofReal (r1*Real.sqrt r1/Real.sqrt r2))) ∧
    ((r1=0 ∧ r2=0) → alpha ![r1,r2]=0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
