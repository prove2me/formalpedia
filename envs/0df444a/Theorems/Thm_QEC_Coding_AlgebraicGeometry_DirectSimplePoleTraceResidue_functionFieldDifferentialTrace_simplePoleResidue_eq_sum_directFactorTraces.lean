-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSimplePoleTraceResidue_functionFieldDifferentialTrace_simplePoleResidue_eq_sum_directFactorTraces
-- name    : QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue.functionFieldDifferentialTrace_simplePoleResidue_eq_sum_directFactorTraces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:52:34.882197+00:00
-- url     : https://prove2.me/theorems/a619dd76-81fc-43f6-8adc-4d90789df917
-- title:
--   Direct Simple Pole Trace Residue: function Field Differential Trace simple Pole Residue eq sum direct Factor Traces
-- statement:
--   Differential trace is compatible with normalized simple-pole residues
--   over every actual factor above one direct finite rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SimplePoleTraceResidue.lean#L145-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SimplePoleTraceResidue.lean#L145-L312

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalDifferentialTraceRegularity
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SimplePoleTraceResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue.simplePoleTraceResidue_Algebra_1
attribute [local instance] simplePoleTraceResidue_Algebra_1
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue.simplePoleTraceResidue_ScalarTower_1
attribute [local instance] simplePoleTraceResidue_ScalarTower_1
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue._p2m_local_instance_fead31de17_60
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue._p2m_local_instance_fead31de17_64
open DirectFactorResidueTransport DirectFactorTraceResidue
open DirectIntegralDifferentialResidue
open DirectSemilocalDifferentialTraceRegularity
open DirectSemilocalSmithTraceResidue
open FunctionFieldDifferential

theorem QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue.functionFieldDifferentialTrace_simplePoleResidue_eq_sum_directFactorTraces
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (omega : Differential k F)
    (homega : ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      omega ∈ Differential.simplePoleDifferentialLattice
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))) :
    ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p),
      Differential.simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          ⟨functionFieldDifferentialTrace (k := k) (F := F) omega, htrace⟩ =
        DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p
          (∑ P : (factors
              (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
            directFactorPlaceTrace k F p P
              (Differential.simplePoleResidue (k := k) (F := F)
                (AffinePlace.globalPlace k F (directFactorPlace k F p P))
                ⟨omega, homega P⟩)) := by sorry
