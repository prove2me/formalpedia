-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_pauli_mul_syndromeProjectorOn
-- name    : QEC.Coding.CSSGibbs.pauli_mul_syndromeProjectorOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:04:53.951832+00:00
-- url     : https://prove2.me/theorems/87abfdf6-75bb-4b5c-a582-c65318deb49a
-- title:
--   CSSGibbs: pauli mul syndrome Projector On
-- statement:
--   Pauli transport through any restricted product of syndrome factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L77-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L77-L133

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

theorem QEC.Coding.CSSGibbs.pauli_mul_syndromeProjectorOn
    (checks : κ → Binary ι) (hcomm : ∀ a b, Commutes (checks a) (checks b))
    (error : Binary ι) (syndrome : JointSyndrome κ)
    (selected : Finset κ) :
    toHermitianQubitOperator error *
        selected.noncommProd (jointStabilizerFactor checks syndrome)
          (syndromeFactor_pairwise checks hcomm syndrome selected) =
      selected.noncommProd
          (jointStabilizerFactor checks
            (transportSyndrome checks hcomm error syndrome))
          (syndromeFactor_pairwise checks hcomm
            (transportSyndrome checks hcomm error syndrome) selected) *
        toHermitianQubitOperator error := by sorry
