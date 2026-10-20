-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_gaussian_oneSided_solvable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.gaussian_oneSided_solvable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:05:33.513888+00:00
-- url     : https://prove2.me/theorems/201e0059-3835-471d-9d50-584b7747d1e8
-- title:
--   §6.3: one-sided Gaussian system is solvable
-- statement:
--   In the finite Gaussian moment representation, let the squeezing drift be \(\operatorname{diag}(-r,r)\), with zero diffusion, and damping have drift \(-\gamma I/2\) and diffusion \(\gamma I/2\). Declare these as two independently actuable one-sided rays and assume \(r\ne0,\gamma>0\). Their actual moment-matrix Lie algebra satisfies
--   \[
--   \dim\mathfrak g=4,\qquad
--   \dim\mathfrak g^{(1)}=2,\qquad \mathfrak g^{(2)}=0.
--   \]
--   It is solvable, so its Levi factor is zero, its radical is the whole algebra, the quotient cone is \(\{0\}\), and FCC is automatic. The supplied squeezing generator is not in the local wedge edge. These statements concern finite moment matrices only.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 38, §6.3: one-sided Gaussian system is solvable

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

namespace QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

open QAlgorithms.Papers.Independent.Information100

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup

/-- arXiv:2608.27330v1, PDF pp.38--39, Section 6.3, one-sided solvable system.
The nondegeneracy assumptions are needed for dimension four. This theorem is
about finite moment matrices only. -/
theorem gaussian_oneSided_solvable (r gamma : ℝ) (hr : r ≠ 0) (hg : 0 < gamma) :
    (let g := LieSubalgebra.lieSpan ℝ (Matrix (Fin 6) (Fin 6) ℝ) (gaussianG r gamma)
     Module.finrank ℝ g = 4 ∧
     Module.finrank ℝ (LieAlgebra.derivedSeries ℝ g 1) = 2 ∧
     LieAlgebra.derivedSeries ℝ g 2 = ⊥ ∧ LieAlgebra.IsSolvable g ∧
     (∀ D : LeviSplitting g, D.s = ⊥ ∧ D.r = ⊤ ∧
       quotientCone D {X : g | (X : Matrix (Fin 6) (Fin 6) ℝ) ∈ minimalWedge (gaussianG r gamma)} = {0} ∧
       FCC D {X : g | (X : Matrix (Fin 6) (Fin 6) ℝ) ∈ minimalWedge (gaussianG r gamma)})) ∧
    squeezeMoment r ∉ edge (minimalWedge (gaussianG r gamma)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
