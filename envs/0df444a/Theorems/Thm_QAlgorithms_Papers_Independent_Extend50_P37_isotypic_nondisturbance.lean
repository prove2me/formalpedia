-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_isotypic_nondisturbance
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.isotypic_nondisturbance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:40:28.268304+00:00
-- url     : https://prove2.me/theorems/8a9f3912-ff8b-4ba6-97b7-1012ed3e0c50
-- title:
--   V B 2: permutation-sector measurement does not disturb iid states
-- statement:
--   Let $d,n\ge1$ and let $\rho$ be a density matrix on $\mathbb C^d$. For the canonical projectors $\Pi_\lambda$ onto the full permutation-isotypic components of the actual tensor representation,
--   $$\sum_\lambda\Pi_\lambda\rho^{\otimes n}\Pi_\lambda=\rho^{\otimes n}.$$
--   Thus forgetting the sector-measurement outcome preserves the state and every subsequent measurement’s statistics. Conditioning on a sector is not claimed to leave the state unchanged.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 24, V B 2: permutation-sector measurement does not disturb iid states

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF p.24: forgetting the canonical permutation-isotypic outcome leaves
the iid state unchanged. This is not conditional-state nondisturbance. -/
theorem isotypic_nondisturbance (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (rho : Mat (Fin d)) (hrho : IsDensityMatrix rho) :
    (∑ lam : Schur.Partition d n, Schur.isotypicProjector lam * piKron n rho *
      Schur.isotypicProjector lam) = piKron n rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
