-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalSmithTraceResidue_exists_directSemilocalSmith_trace_residue_sum_compatibility
-- name    : QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue.exists_directSemilocalSmith_trace_residue_sum_compatibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:50:41.500164+00:00
-- url     : https://prove2.me/theorems/c1a3c94e-be0e-4344-8dee-392ddc110932
-- title:
--   Direct Semilocal Smith Trace Residue: exists direct Semilocal Smith trace residue sum compatibility
-- statement:
--   Smith data can be chosen for one simultaneous order-one integral element
--   so that its Smith differential is the actual differential trace and its
--   rational residue is the transported full upper factor-residue sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalSmithTraceResidue.lean#L143-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalSmithTraceResidue.lean#L143-L197

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalCokernelTraceSum
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalSmithTraceResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_38
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_40
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_50
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_54
open DirectFactorSmithTraceResidue

theorem QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue.exists_directSemilocalSmith_trace_residue_sum_compatibility
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (b : B k F) :
    ∃ t : B k F, ∃ ht : t ≠ 0,
      ∃ source target : Module.Basis
        (Fin (Module.finrank (R k) (B k F))) (R k) (B k F),
      ∃ a : Fin (Module.finrank (R k) (B k F)) → R k,
      ∃ ha : ∀ i, a i ≠ 0,
        LinearMap.toMatrix source target
            (Algebra.lmul (R k) (B k F) t) = Matrix.diagonal a ∧
        (∀ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          GlobalPlace.order
              (AffinePlace.globalPlace k F
                (DirectIntegralDifferentialResidue.directFactorPlace k F p P))
              (algebraMap (B k F) F t) = 1) ∧
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
            (∑ P : (factors
                (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
              Ideal.Factors.factorResidueTrace p.asIdeal P b) := by sorry
