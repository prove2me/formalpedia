-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_protected_univ
-- name    : QEC.Coding.BDL26PairedDecoderPhase.protected_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:58:10.603067+00:00
-- url     : https://prove2.me/theorems/2e2fad96-54bb-4705-a35a-6f449d3dd862
-- title:
--   BDL26 Paired Decoder Phase: protected univ
-- statement:
--   The BDL26 Paired Decoder Phase construction uses the protected univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L330-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderPhase.lean#L330-L344

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

theorem QEC.Coding.BDL26PairedDecoderPhase.protected_univ (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∀ s : Visible S n, ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∀ s : Visible S n, ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) :
    Commute (toHermitianQubitOperator E) (dressed S n logical) := by sorry
