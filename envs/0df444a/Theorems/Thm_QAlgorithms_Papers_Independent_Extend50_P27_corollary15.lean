-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_corollary15
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.corollary15
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:44:46.660662+00:00
-- url     : https://prove2.me/theorems/1c3e4459-23e8-437c-9806-b2c05524bbf6
-- title:
--   Corollary 15: primitivity
-- statement:
--   Let $N\ge1$. The full teleportation matrix $M_N$ is indexed by all $N$-box Young diagrams, with removable-corner counts on the diagonal and one on distinct single-box-move pairs. For $d\ge1$, $M_N^{(d)}$ is its principal restriction to shapes of height at most $d$, retaining the same diagonal counts.
--
--   Both matrices are primitive: each is nonnegative and admits a positive integer $q$ such that
--
--   $$\forall i,j,\quad (M^q)_{ij}>0.$$
--
--   For finite nonnegative matrices this is equivalent to the source's irreducible, unique nonzero peripheral-eigenvalue formulation. It supplies the power-iteration convergence condition.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 12, Corollary 15: primitivity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Corollary 15: finite nonnegative primitivity, expressed by a strictly positive
power, equivalent to the source's peripheral-spectrum definition (PDF pp.12,30). -/
theorem corollary15 {d N : ℕ} (hd : 0 < d) (hN : 0 < N) :
    (fullMatrix N).IsPrimitive ∧ (teleportMatrix d N).IsPrimitive := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
