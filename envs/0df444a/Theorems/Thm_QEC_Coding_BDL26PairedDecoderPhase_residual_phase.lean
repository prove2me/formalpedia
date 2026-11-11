-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_residual_phase
-- name    : QEC.Coding.BDL26PairedDecoderPhase.residual_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:34:45.264195+00:00
-- url     : https://prove2.me/theorems/3d97e3f8-75a8-4005-ac45-61a30599a19f
-- title:
--   BDL26 Paired Decoder Phase: residual phase
-- statement:
--   Neither the old background nor the post-error Z overlap is discarded.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L66-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L66-L72

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

theorem QEC.Coding.BDL26PairedDecoderPhase.residual_phase (s : Visible S n) (E : Binary (Physical S (n + 2))) :
    (residual S n s E).phase = E.phase +
      (∑ q, xCorrection S n s.1 q * E.vector.zPart q) +
      ∑ q, (E.vector.xPart q + xCorrection S n s.1 q) *
        zCorrection S n (translation S n E s).2 q := by sorry
