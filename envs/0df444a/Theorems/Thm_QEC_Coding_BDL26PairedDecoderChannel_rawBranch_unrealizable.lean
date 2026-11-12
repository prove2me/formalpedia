-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_rawBranch_unrealizable
-- name    : QEC.Coding.BDL26PairedDecoderChannel.rawBranch_unrealizable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:40:23.593352+00:00
-- url     : https://prove2.me/theorems/c30fdc1b-5db9-4dbd-9643-cb2aa72ff6dc
-- title:
--   BDL26 Paired Decoder Channel: raw Branch unrealizable
-- statement:
--   The BDL26 Paired Decoder Channel construction uses the raw Branch unrealizable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L172-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderChannel.lean#L172-L182

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderChannel
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderChannel._p2m_local_instance_c895a38b5b_28
attribute [local instance] QEC.Coding.BDL26PairedDecoderChannel._p2m_local_instance_c895a38b5b_29

theorem QEC.Coding.BDL26PairedDecoderChannel.rawBranch_unrealizable
    (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2))))
    (hw : w ∉ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2)))
    (A : Op S n) : rawBranch S n w A = 0 := by sorry
