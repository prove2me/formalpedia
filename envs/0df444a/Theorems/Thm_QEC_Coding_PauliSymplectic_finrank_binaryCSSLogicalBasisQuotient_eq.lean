-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_finrank_binaryCSSLogicalBasisQuotient_eq
-- name    : QEC.Coding.PauliSymplectic.finrank_binaryCSSLogicalBasisQuotient_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:07.865191+00:00
-- url     : https://prove2.me/theorems/39757a3c-e952-4426-bc41-5ed338b85111
-- title:
--   Pauli Symplectic: finrank binary CSSLogical Basis Quotient eq
-- statement:
--   The algebraic binary CSS logical-basis quotient has dimension
--   `n - dim xCode - dim zCode`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2005-L2017
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2005-L2017

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
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.finrank_binaryCSSLogicalBasisQuotient_eq
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    Module.finrank (ZMod 2) (binaryCSSLogicalBasisQuotient xCode zCode) =
      Length (ZMod 2) ι - Dimension xCode - Dimension zCode := by sorry
