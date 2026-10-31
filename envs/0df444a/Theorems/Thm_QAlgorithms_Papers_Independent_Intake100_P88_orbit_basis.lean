-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_orbit_basis
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.orbit_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:35:17.279282+00:00
-- url     : https://prove2.me/theorems/90e90dd4-95e2-447c-8a0e-87a32a66dc68
-- title:
--   Unnumbered (2.3): orbit basis
-- statement:
--   Let $\ell\ge0$ be a half-integer, and let $\mathbb C A_\ell$ be the complex vector space freely spanned by its partition diagrams. Order diagrams by refinement, so $d\le e$ means that every block of $d$ is contained in a block of $e$. There is a unique basis $(x_d)_{d\in A_\ell}$ satisfying
--
--   $$d=\sum_{e\,\ge d}x_e\qquad(d\in A_\ell).$$
--
--   This is the orbit basis used by the exact-equality tensor matrices. The summation uses coarsenings, correcting the reversed inequality printed in (2.3); the correction is forced by (3.8).
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 10, Unnumbered (2.3): orbit basis

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Unique orbit basis, PDF pp.9--10, (2.3).
SOURCE CORRECTION: sum over coarsenings, as forced by exact-equality matrices (3.8),
rather than the printed reversed refinement inequality. -/
theorem orbit_basis (m : ℕ) :
    ∃! b : Module.Basis (LevelDiagram m) ℂ (DiagramSpace m),
      ∀ d : LevelDiagram m,
        Finsupp.single d 1 = ∑ e ∈ Finset.univ.filter (fun e : LevelDiagram m => d.val ≤ e.val), b e := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
