-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_residual_commutes
-- name    : QEC.Coding.BDL26PairedDecoderPhase.residual_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:35:43.458999+00:00
-- url     : https://prove2.me/theorems/1c20a740-0e86-4ff4-91ad-e292681cfdf8
-- title:
--   BDL26 Paired Decoder Phase: residual commutes
-- statement:
--   The stored residual sign is harmless for commutation, but remains stored.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L85-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L85-L93

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

theorem QEC.Coding.BDL26PairedDecoderPhase.residual_commutes (s : Visible S n) (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) : Commutes (residual S n s E) logical := by sorry
