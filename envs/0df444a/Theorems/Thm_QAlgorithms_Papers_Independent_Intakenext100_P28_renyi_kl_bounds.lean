-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_renyi_kl_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.renyi_kl_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:53:52.766638+00:00
-- url     : https://prove2.me/theorems/78bd3306-75d9-4ba7-a8de-509b0e6b8373
-- title:
--   Theorem 38: All Renyi-versus-KL bounds (512)–(517), in the regimes 0<alpha<1 and alpha>1, plus the TV-derived bound using delta_bar^2=min{D/(2log e),1-exp(-D)}
-- statement:
--   Let $P\ll Q$, $\beta_1,\beta_2<1$, $\alpha>0$, $\alpha\ne1$, and put $u_\alpha(t)=(\alpha-1)/\kappa_\alpha(t)$ with kernel (176). Set $T(t)=\log_b((1+u_\alpha(t)D)^+)/(\alpha-1)$, where $D=D(P\|Q)$ and $\log_b0=-\infty$. For $\alpha<1$,
--
--   $$T(\beta_1^{-1})\le D_\alpha\le\min\{D,T(\beta_2)\}.$$
--
--   For $\alpha>1$, $\max\{D,T(\beta_2)\}\le D_\alpha\le\min\{\log_b(1/\beta_1),T(\beta_1^{-1})\}$. In both regimes,
--
--   $$D_\alpha\le\frac1{\alpha-1}\log_b\left(1+\bar\delta\frac{\beta_1^{1-\alpha}-1}{1-\beta_1}\right),\quad
--   \bar\delta^2=\min\{D/(2\log_b e),1-\exp_b(-D)\}.$$
--
--   The coefficient $u_\alpha$ is signed, negative for $\alpha<1$; the source's nonnegative codomain is corrected. Infinite scalar endpoints use the kernel's continuous limits and extended logarithms. All bounds (512)–(517) are included.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 71, Theorem 38

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 38: All Renyi-versus-KL bounds (512)–(517), in the regimes 0<alpha<1 and alpha>1, plus the TV-derived bound using delta_bar^2=min{D/(2log e),1-exp(-D)}. Sason--Verdu, arXiv:1508.00335v7, PDF p.71. Source correction: u_alpha takes signed extended values for alpha<1; the printed [0,infinity] codomain in (511) is false. Positive part is applied inside log, as in (513). -/
theorem renyi_kl_bounds
    (b : LogBase) (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hb1 : inverseUpperDensity P Q < 1) (hb2 : inverseUpperDensity Q P < 1) :
    (a < 1 → renyiLower b a P Q ≤ renyiDiv b a P Q ∧ renyiDiv b a P Q ≤ renyiUpper b a P Q) ∧
    (1 < a → renyiLower b a P Q ≤ renyiDiv b a P Q ∧ renyiDiv b a P Q ≤ renyiUpper b a P Q) ∧
    renyiDiv b a P Q ≤ renyiDeltaBound b a (inverseUpperDensity P Q) (deltaBar b (kl b P Q)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
