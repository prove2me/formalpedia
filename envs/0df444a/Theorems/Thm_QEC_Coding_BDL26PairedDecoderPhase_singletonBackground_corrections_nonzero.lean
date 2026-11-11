-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_singletonBackground_corrections_nonzero
-- name    : QEC.Coding.BDL26PairedDecoderPhase.singletonBackground_corrections_nonzero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:27:45.73997+00:00
-- url     : https://prove2.me/theorems/ae74dcf8-74e3-4734-8c6e-da5fec7db59d
-- title:
--   BDL26 Paired Decoder Phase: singleton Background corrections nonzero
-- statement:
--   The actual right inverses force both computed corrections to be nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L388-L399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L388-L399

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

theorem QEC.Coding.BDL26PairedDecoderPhase.singletonBackground_corrections_nonzero (q : Physical S (n + 2)) :
    xCorrection S n (singletonBackground S n q).1 ≠ 0 ∧
      zCorrection S n (singletonBackground S n q).2 ≠ 0 := by sorry
