-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_symmetric_cloning_maximum
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.symmetric_cloning_maximum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:26:53.41302+00:00
-- url     : https://prove2.me/theorems/cda4520d-cea9-4faa-aaf1-dffd3cf4b750
-- title:
--   Attained maximal symmetric shrink factor
-- statement:
--   For every integer $d\ge2$, put $p_{\max}=(d+2)/(2(d+1))$. There exists a restricted four-permutation CPTP cloner with both depolarizing marginal parameters equal to $p_{\max}$, and every unrestricted CPTP cloner with two equal parameters $p$ satisfies
--
--   $$
--   p\le p_{\max}=\frac{d+2}{2(d+1)}.
--   $$
--
--   The associated constant pure-input fidelity is $p+(1-p)/d$. At $d=2$ the maximum shrink factor is $2/3$, giving fidelity $5/6$.
--
--   Thus the symmetric optimum is attained within the restricted family. The source attributes this numerical value to Werner [Wer98].
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 10, Unnumbered attained maximum symmetric cloning quality

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

/-- PDF p.10, with global optimality from pp.12–13: the attained symmetric maximum.
The source credits the numerical value to Werner [Wer98]; it is not a novelty claim here. -/
theorem symmetric_cloning_maximum (d : ℕ) (hd : 2 ≤ d) :
    RestrictedAchievable d (((d : ℝ) + 2) / (2 * ((d : ℝ) + 1)))
      (((d : ℝ) + 2) / (2 * ((d : ℝ) + 1))) ∧
    ∀ p : ℝ, CloningAchievable d p p → p ≤ ((d : ℝ) + 2) / (2 * ((d : ℝ) + 1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
