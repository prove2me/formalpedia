-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseSimplePoleTraceResidue_simplePoleTraceResidue_rationalDifferentialInvolution_reverse
-- name    : QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue.simplePoleTraceResidue_rationalDifferentialInvolution_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:53:02.811207+00:00
-- url     : https://prove2.me/theorems/0a5e7b27-88a8-4a24-8a41-aac10d1643db
-- title:
--   Inverse Simple Pole Trace Residue: simple Pole Trace Residue rational Differential Involution reverse
-- statement:
--   Reverse traced-residue compatibility for rational coordinate inversion:
--   simple-pole membership at `(X)` transports back to rational infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/SimplePoleTraceResidue.lean#L125-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/SimplePoleTraceResidue.lean#L125-L208

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SimplePoleTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_DifferentialTraceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_SimplePoleTraceResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
open scoped Polynomial RatFunc BigOperators
open FunctionFieldDifferential
open UniqueFactorizationMonoid
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue.simplePoleTraceResidue_rationalDifferentialInvolution_reverse
    (eta : Differential k (RatFunc k))
    (heta : eta ∈ Differential.simplePoleDifferentialLattice
      (InverseRationalInfinityTransport.xAdicPlace k)) :
    ∃ hback :
        InverseRationalInfinityTransport.rationalDifferentialInvolution
            (k := k) eta ∈
          Differential.simplePoleDifferentialLattice
            (GlobalPlace.rationalInfinity k),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalInfinity k)
          (InverseRationalInfinityTransport.rationalDifferentialInvolution
            (k := k) eta) hback =
        Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (InverseRationalInfinityTransport.xAdicPlace k) eta heta := by sorry
