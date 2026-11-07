-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_multiplicity_mul_card_realizable
-- name    : QEC.Coding.CSSGibbs.multiplicity_mul_card_realizable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:06:03.001695+00:00
-- url     : https://prove2.me/theorems/29ffd0ad-db25-446e-97a5-df26ed13cdb1
-- title:
--   CSSGibbs: multiplicity mul card realizable
-- statement:
--   The CSSGibbs construction uses the multiplicity mul card realizable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L67-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L67-L72

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_ea4515a18e_14
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_ea4515a18e_15
include horth

theorem QEC.Coding.CSSGibbs.multiplicity_mul_card_realizable :
    multiplicity P Q * Fintype.card (Realizable P Q) = 2 ^ Fintype.card ι := by sorry
