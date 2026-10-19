-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_leastAdmissible_exists
-- name    : QAlgorithms.Papers.Independent.Information100.P07.leastAdmissible_exists
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:39:15.088986+00:00
-- url     : https://prove2.me/theorems/9e39101c-e597-4050-86c7-c5ac5e969dd9
-- title:
--   Unnumbered: unique least admissible projector and intrinsic support
-- statement:
--   Let $\rho$ be an entangled two-qutrit state. A product orthogonal projector $R=P\otimes Q$ is admissible if each local rank is two or three, $[\rho,R]=0$, and $\rho-R\rho R\in\mathrm{SEP}$. Construct $R_*(\rho)$ as the orthogonal projector onto the intersection of all admissible ranges. Then it is admissible and is the unique least admissible projector under range inclusion. For $C=R_*\rho R_*$,
--   $$P_{\operatorname{supp}\operatorname{Tr}_B C}\otimes P_{\operatorname{supp}\operatorname{Tr}_A C}=R_*.$$
--
--   Thus the least block has exactly the intrinsic local supports of its defining rectangle. The identity is an admissible member, so the intersection family is nonempty. The retained block is positive, nonzero and outside SEP, and its weight lies in (0,1].
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 3, Unnumbered: unique least admissible projector and intrinsic support

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF pp.3,18–19: intersection gives the unique least admissible projection and its nonzero entangled positive block with weight in (0,1]. -/
theorem leastAdmissible_exists (rho : Joint) (hrho : Entangled rho) :
    Admissible rho (leastProjection rho) ∧ operatorRange (leastProjection rho) = leastRange rho ∧
    (∀ R, Admissible rho R → operatorRange (leastProjection rho) ≤ operatorRange R) ∧
    (∀ R, Admissible rho R → (∀ S, Admissible rho S → operatorRange R ≤ operatorRange S) →
      R = leastProjection rho) ∧
    Matrix.kronecker (support (traceRight (retainedBlock rho)))
      (support (traceLeft (retainedBlock rho))) = leastProjection rho ∧
    (retainedBlock rho).PosSemidef ∧ retainedBlock rho ≠ 0 ∧
    ¬ IsSeparablePositive (retainedBlock rho) ∧
    0 < retainedWeight rho ∧ retainedWeight rho ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
