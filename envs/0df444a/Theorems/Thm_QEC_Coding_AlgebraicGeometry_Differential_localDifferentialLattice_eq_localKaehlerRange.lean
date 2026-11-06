-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_localDifferentialLattice_eq_localKaehlerRange
-- name    : QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice_eq_localKaehlerRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:15:23.406693+00:00
-- url     : https://prove2.me/theorems/9020892d-e5cf-46b9-9cbd-b50d7c267bc1
-- title:
--   Differential: local Differential Lattice eq local Kaehler Range
-- statement:
--   The actual local differential lattice is the range of the map from local
--   Kähler differentials induced by the function-field universal derivation.  The
--   constant-field algebra and scalar tower on the valuation ring are theorem-local,
--   so this equality exports no ambient instance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L95-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L95-L119

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
open QEC.Coding.AlgebraicGeometry.Differential

theorem QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice_eq_localKaehlerRange
    (P : GlobalPlace k F) :
    letI : Algebra k P.valuationRing :=
      (GlobalPlace.constantsToValuationRing P).toAlgebra
    letI : IsScalarTower k P.valuationRing F :=
      IsScalarTower.of_algebraMap_eq fun c => by
        change algebraMap k F c =
          ((GlobalPlace.constantsToValuationRing P c : P.valuationRing) : F)
        exact (GlobalPlace.coe_constantsToValuationRing P c).symm
    localDifferentialLattice P =
      (Derivation.liftKaehlerDifferential
        (Derivation.compAlgebraMap (A := P.valuationRing)
          (KaehlerDifferential.D k F))).range := by sorry
