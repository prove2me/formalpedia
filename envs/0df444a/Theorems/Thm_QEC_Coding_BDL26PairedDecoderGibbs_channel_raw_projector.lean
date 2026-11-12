-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_raw_projector
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.channel_raw_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:28:29.069198+00:00
-- url     : https://prove2.me/theorems/b8a49f7a-e37f-4bcb-a5d8-45e720e00815
-- title:
--   BDL26 Paired Decoder Gibbs: channel raw projector
-- statement:
--   Raw unreachable labels retain their zero input projector and zero output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L102-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L102-L115

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24

theorem QEC.Coding.BDL26PairedDecoderGibbs.channel_raw_projector
    (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2)))) :
    channel S n (projector S (n+2) w) =
      if w ∈ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2))
      then groundProjector S n else 0 := by sorry
