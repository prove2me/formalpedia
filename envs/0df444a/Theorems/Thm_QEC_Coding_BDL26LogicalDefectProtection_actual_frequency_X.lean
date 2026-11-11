-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_actual_frequency_X
-- name    : QEC.Coding.BDL26LogicalDefectProtection.actual_frequency_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:34:59.523177+00:00
-- url     : https://prove2.me/theorems/cb477058-1d26-451e-9818-d8709672972a
-- title:
--   BDL26 Logical Defect Protection: actual frequency X
-- statement:
--   Original frequency sign and all real frequencies are inherited unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L535-L545
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectProtection.lean#L535-L545

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_23
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_24

theorem QEC.Coding.BDL26LogicalDefectProtection.actual_frequency_X (q : Physical S (n+2)) (axis : CSSDaviesLocality.Axis) (omega : ℝ) :
    (Davies.actualFrequency (hamiltonian S (n+2)) (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega * BDL26PairedDecoderChannel.dressedX S n -
      BDL26PairedDecoderChannel.dressedX S n * Davies.actualFrequency (hamiltonian S (n+2))
        (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
          (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega) * protectedProjector S n = 0 := by sorry
