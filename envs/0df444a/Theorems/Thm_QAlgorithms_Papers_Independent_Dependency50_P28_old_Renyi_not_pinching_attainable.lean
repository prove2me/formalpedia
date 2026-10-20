-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_old_Renyi_not_pinching_attainable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.old_Renyi_not_pinching_attainable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:14:55.958813+00:00
-- url     : https://prove2.me/theorems/be47374d-0ec6-41f4-b255-4f54255b1c73
-- title:
--   Old Renyi divergences fail asymptotic pinching and measurement attainability
-- statement:
--   Let α>0 with α≠1. For finite-dimensional density operators, let Doldα denote the Petz Rényi divergence (3), with natural logarithms, support-restricted powers, and the source’s infinity convention. AAP means normalized asymptotic attainment by reference-state pinching on tensor powers; AAM means normalized asymptotic attainment by some sequence of finite measurements, for every state pair. Then
--
--   $$
--   \neg\operatorname{AAP}(D^{\mathrm{old}}_\alpha),\qquad \alpha\geq\tfrac12\ \Longrightarrow\ \neg\operatorname{AAM}(D^{\mathrm{old}}_\alpha).
--   $$
--
--   Each failure asserts the existence of a state pair violating the corresponding universal attainment property.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 22, :

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.22: Old Renyi divergences fail asymptotic pinching attainability for every positive nonunit order, and asymptotic measurement attainability for orders at least one-half other than one. Both failures are existential over state pairs. Full-rank noncommuting pairs avoid unjustified strictness at infinite divergences. The measurement clause continues on PDF p.23. -/
theorem old_Renyi_not_pinching_attainable (alpha : ℝ) (ha : 0 < alpha) (hne : alpha ≠ 1) :
    ¬ AAP (oldFamily alpha) ∧ ((1 / 2 : ℝ) ≤ alpha → ¬ AAM (oldFamily alpha)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
