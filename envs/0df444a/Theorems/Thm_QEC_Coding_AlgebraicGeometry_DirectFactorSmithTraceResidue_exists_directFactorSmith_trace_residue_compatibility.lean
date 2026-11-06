-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_exists_directFactorSmith_trace_residue_compatibility
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.exists_directFactorSmith_trace_residue_compatibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:45:47.446992+00:00
-- url     : https://prove2.me/theorems/8d0563cd-1ffc-4f90-b76c-ec2db090b082
-- title:
--   Direct Factor Smith Trace Residue: exists direct Factor Smith trace residue compatibility
-- statement:
--   Smith bases and a semilocal multiplier can be chosen so that the same
--   actual Smith differential is the differential trace of `b * dt/t`, while its
--   rational residue is the transported traced residue at the selected factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSmithTraceResidue.lean#L177-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSmithTraceResidue.lean#L177-L234

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSmithTraceResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_37
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_49
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_53
open DirectIntegralDifferentialResidue DirectFactorTraceResidue
open DirectFactorSemilocalLogarithmicResidue

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.exists_directFactorSmith_trace_residue_compatibility
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    ∃ t : B k F, ∃ ht : t ≠ 0,
      ∃ source target : Module.Basis
        (Fin (Module.finrank (R k) (B k F))) (R k) (B k F),
      ∃ a : Fin (Module.finrank (R k) (B k F)) → R k,
      ∃ ha : ∀ i, a i ≠ 0,
        LinearMap.toMatrix source target
            (Algebra.lmul (R k) (B k F) t) = Matrix.diagonal a ∧
        GlobalPlace.order
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (algebraMap (B k F) F t) = 1 ∧
        ((Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
            source target a ha (Algebra.lmul (R k) (B k F) b) :
              Differential.simplePoleDifferentialLattice
                (GlobalPlace.rationalAdic p)) :
            Differential k (RatFunc k)) =
          FunctionFieldDifferential.functionFieldDifferentialTrace
            (k := k) (F := F)
            ((algebraMap (B k F) F b) •
              Differential.logarithmicDifferential (k := k) (F := F)
                (algebraMap (B k F) F t)) ∧
        Differential.simplePoleResidue (k := k) (F := RatFunc k)
            (GlobalPlace.rationalAdic p)
            (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole
              p source target a ha (Algebra.lmul (R k) (B k F) b)) =
          directBaseResidueRationalAdicEquiv k p
            (directFactorPlaceTrace k F p P
              (Differential.simplePoleResidue (k := k) (F := F)
                (AffinePlace.globalPlace k F (directFactorPlace k F p P))
                (directFactorSemilocalLogarithmicDifferentialAtSimplePole
                  k F p P t ht b))) := by sorry
