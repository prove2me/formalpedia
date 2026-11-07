-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_pauli_mul_jointStabilizerFactor
-- name    : QEC.Coding.CSSGibbs.pauli_mul_jointStabilizerFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:04:18.290206+00:00
-- url     : https://prove2.me/theorems/eb1a4c8f-35c1-4bda-b562-da4292ed929c
-- title:
--   CSSGibbs: pauli mul joint Stabilizer Factor
-- statement:
--   One Pauli transports one selected spectral factor to the flipped sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L40-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L40-L64

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

theorem QEC.Coding.CSSGibbs.pauli_mul_jointStabilizerFactor
    (checks : κ → Binary ι) (hcomm : ∀ a b, Commutes (checks a) (checks b))
    (error : Binary ι) (syndrome : JointSyndrome κ) (check : κ) :
    toHermitianQubitOperator error *
        jointStabilizerFactor checks syndrome check =
      jointStabilizerFactor checks
          (transportSyndrome checks hcomm error syndrome) check *
        toHermitianQubitOperator error := by sorry
