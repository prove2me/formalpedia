-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_transport_zero
-- name    : QEC.Coding.CSSGibbs.transport_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:05:17.034389+00:00
-- url     : https://prove2.me/theorems/ba644b6b-b0ae-413d-a990-c64e31c00979
-- title:
--   CSSGibbs: transport zero
-- statement:
--   All-plus transport is precisely the existing binary commutation syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L274-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L274-L280

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {κP κQ : Type} [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)

theorem QEC.Coding.CSSGibbs.transport_zero (E : Binary ι) :
    transportSyndrome (binaryCSSParityCheckGenerators P Q) (checks_commute P Q horth)
      E (syndromeOutcome _ 0) =
      syndromeOutcome _ (stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E) := by sorry
