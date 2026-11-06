-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_finset_sum
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_finset_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:39:12.495089+00:00
-- url     : https://prove2.me/theorems/2d57143c-23d8-4fe5-b0f0-6bfd57e38e32
-- title:
--   Differential: global Simple Pole Residue Sum finset sum
-- statement:
--   The global residue sum of a finite sum is the finite sum of the global
--   residue sums.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L124-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L124-L152

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_finset_sum {ι : Type*} (s : Finset ι)
    (omega : ι → Differential k F)
    (homega : ∀ i, IsGlobalSimplePole (k := k) (F := F) (omega i)) :
    globalSimplePoleResidueSum (k := k) (F := F) (∑ i ∈ s, omega i)
        (IsGlobalSimplePole.finset_sum s omega homega) =
      ∑ i ∈ s, globalSimplePoleResidueSum (k := k) (F := F)
        (omega i) (homega i) := by sorry
