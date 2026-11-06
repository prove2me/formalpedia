-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_simplePoleResidue_rationalAdicSmith_eq_directFactorTrace
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.simplePoleResidue_rationalAdicSmith_eq_directFactorTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:45:44.445821+00:00
-- url     : https://prove2.me/theorems/08d0454f-897f-4097-a659-9cb63e40ea73
-- title:
--   Direct Factor Smith Trace Residue: simple Pole Residue rational Adic Smith eq direct Factor Trace
-- statement:
--   For supplied Smith data of a semilocal multiplier, the rational-place
--   Smith residue is the canonical transport of the traced normalized residue at
--   the selected upper factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSmithTraceResidue.lean#L92-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSmithTraceResidue.lean#L92-L172

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

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.simplePoleResidue_rationalAdicSmith_eq_directFactorTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0) (b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J)
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
        (directFactorPlaceTrace k F p P
          (Differential.simplePoleResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (directFactorSemilocalLogarithmicDifferentialAtSimplePole
              k F p P t ht b))) := by sorry
