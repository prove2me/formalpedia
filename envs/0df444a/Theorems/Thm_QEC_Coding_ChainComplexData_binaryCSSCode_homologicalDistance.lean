-- Prove2me | Theorems.Thm_QEC_Coding_ChainComplexData_binaryCSSCode_homologicalDistance
-- name    : QEC.Coding.ChainComplexData.binaryCSSCode_homologicalDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:29:00.943332+00:00
-- url     : https://prove2.me/theorems/08a61d64-a20c-4520-8587-27a6c6c9249d
-- title:
--   Chain Complex Data: binary CSSCode homological Distance
-- statement:
--   For a finite based binary chain complex, the associated CSS code has pure-X
--   logical quotient equivalent to middle cohomology and pure-Z logical quotient
--   equivalent to middle homology, with the displayed equations recording the
--   action on representatives. Exact minima in the two logical sectors give
--   algebraic CSS distance `min dX dZ`.
--
--   This uses the source's transpose orientation directly and does not identify
--   homology and cohomology through a Hamming-weight-preserving pairing.
--
--   [BE20, Sections II.A-II.B]
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2981-L3000
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2981-L3000

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.ChainComplexData

theorem QEC.Coding.ChainComplexData.binaryCSSCode_homologicalDistance
    {ι κ lambda : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) (Word (ZMod 2) lambda))
    {dX dZ : Nat}
    (hX : PureXLogicalMinimumDistance
      (K.binaryCSSCode).xCode (K.binaryCSSCode).zCode dX)
    (hZ : PureZLogicalMinimumDistance
      (K.binaryCSSCode).xCode (K.binaryCSSCode).zCode dZ) :
    (∀ x : K.middleBoundaryCode.dual.carrier,
      K.pureXLogicalQuotientEquivMiddleCohomology (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk (K.middleBoundaryDualEquivMiddleCocycleCode x)) ∧
    (∀ z : K.firstCoboundaryCheckCode.dual.carrier,
      K.pureZLogicalQuotientEquivMiddleHomology (Submodule.Quotient.mk z) =
        Submodule.Quotient.mk (K.firstCoboundaryDualEquivMiddleCycleCode z)) ∧
    AlgebraicCSSMinimumDistance
      (K.binaryCSSCode).xCode (K.binaryCSSCode).zCode (min dX dZ) := by sorry
