-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_coupling_protected_atom
-- name    : QEC.Coding.BDL26PairedDecoderPhase.coupling_protected_atom
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:56:53.714209+00:00
-- url     : https://prove2.me/theorems/27a28aa6-e8ff-4237-987b-90b806b181bd
-- title:
--   BDL26 Paired Decoder Phase: coupling protected atom
-- statement:
--   Literal XYZ couplings, on the same Hamiltonian and register.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L347-L356
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L347-L356

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

theorem QEC.Coding.BDL26PairedDecoderPhase.coupling_protected_atom (s : Visible S n) (q : Physical S (n + 2))
    (axis : CSSDaviesLocality.Axis) (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s (CSSDaviesLocality.singlePauli q axis)).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s (CSSDaviesLocality.singlePauli q axis)).vector.zPart) :
    (BDL26CSSDaviesLocality.coupling S (n + 2) q axis * dressed S n logical -
      dressed S n logical * BDL26CSSDaviesLocality.coupling S (n + 2) q axis) * atom S n s = 0 := by sorry
