-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalSmithTraceResidue_simplePoleResidue_rationalAdicSmith_eq_sum_factorResidueTraces
-- name    : QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue.simplePoleResidue_rationalAdicSmith_eq_sum_factorResidueTraces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:50:51.367203+00:00
-- url     : https://prove2.me/theorems/0cc79bb1-39aa-4d7c-a556-bd7013af7365
-- title:
--   Direct Semilocal Smith Trace Residue: simple Pole Residue rational Adic Smith eq sum factor Residue Traces
-- statement:
--   For supplied Smith data of a simultaneous principal factorization, the
--   rational Smith residue is the canonical transport of the complete sum of
--   upper factor-residue traces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalSmithTraceResidue.lean#L72-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalSmithTraceResidue.lean#L72-L138

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

theorem QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue.simplePoleResidue_rationalAdicSmith_eq_sum_factorResidueTraces
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (∏ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          (P : Ideal (B k F))) * J)
    {n : ℕ}
    (source target : Module.Basis (Fin n) (R k) (B k F))
    (a : Fin n → R k) (ha : ∀ i, a i ≠ 0)
    (hdiag : LinearMap.toMatrix source target
      (Algebra.lmul (R k) (B k F) t) = Matrix.diagonal a) :
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha (Algebra.lmul (R k) (B k F) b)) =
      directBaseResidueRationalAdicEquiv k p
        (∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          Ideal.Factors.factorResidueTrace p.asIdeal P b) := by sorry
