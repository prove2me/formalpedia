-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectIntegralDifferentialResidue_directFactorPlace_order_baseGenerator
-- name    : QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace_order_baseGenerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:37:25.42843+00:00
-- url     : https://prove2.me/theorems/6ac50a53-a0e1-4f66-aaac-0ee3afcbba72
-- title:
--   Direct Integral Differential Residue: direct Factor Place order base Generator
-- statement:
--   At an actual upper factor place, the normalized order of the chosen base
--   prime generator is precisely the ramification index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralDifferentialResidue.lean#L73-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralDifferentialResidue.lean#L73-L109

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue
open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue._p2m_local_instance_3e6bb6d2a4_37
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue._p2m_local_instance_3e6bb6d2a4_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue._p2m_local_instance_3e6bb6d2a4_49

theorem QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace_order_baseGenerator
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    GlobalPlace.order (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (algebraMap (R k) F (generator p.asIdeal)) =
      (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) : ℤ) := by sorry
