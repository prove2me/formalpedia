-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_actual_truncated_counterexample
-- name    : QEC.Coding.BDL26PairedDecoderPhase.actual_truncated_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:34:42.4714+00:00
-- url     : https://prove2.me/theorems/3ce2c0c2-2079-4f9e-bde9-89f4df675c8d
-- title:
--   BDL26 Paired Decoder Phase: actual truncated counterexample
-- statement:
--   A fully actual counterexample to truncating the full phase sum before restriction.
--   The same two zero-witness residual boundary premises protect the full global O.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L585-L603
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L585-L603

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderPhase
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderPhase._p2m_local_instance_6635fd3be7_27
attribute [local instance] QEC.Coding.BDL26PairedDecoderPhase._p2m_local_instance_6635fd3be7_28

theorem QEC.Coding.BDL26PairedDecoderPhase.actual_truncated_counterexample (q : Physical S (n + 2)) :
    let s : Visible S n := 0
    let t := singletonBackground S n q
    let E := bridgeError S n s t
    translation S n E s = t ∧
    (∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a = (residual S n s E).vector.xPart) ∧
    (∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b = (residual S n s E).vector.zPart) ∧
    (toHermitianQubitOperator E * dressed S n binaryOne -
      dressed S n binaryOne * toHermitianQubitOperator E) * atom S n s = 0 ∧
    (toHermitianQubitOperator E *
        (∑ a ∈ ({s} : Finset (Visible S n)), commutationPhase (correction S n a) binaryOne • atom S n a) -
      (∑ a ∈ ({s} : Finset (Visible S n)), commutationPhase (correction S n a) binaryOne • atom S n a) *
        toHermitianQubitOperator E) * atom S n s ≠ 0 := by sorry
