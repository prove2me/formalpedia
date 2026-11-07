-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_sector_finrank_zero_of_not_realizable
-- name    : QEC.Coding.CSSGibbs.sector_finrank_zero_of_not_realizable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:07:22.425241+00:00
-- url     : https://prove2.me/theorems/f014caaa-e8d5-4762-b472-6bd0f2cadb0b
-- title:
--   CSSGibbs: sector finrank zero of not realizable
-- statement:
--   The CSSGibbs construction uses the sector finrank zero of not realizable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L155-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L155-L159

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

theorem QEC.Coding.CSSGibbs.sector_finrank_zero_of_not_realizable (s : Word (ZMod 2) (Sum κP κQ))
    (hs : s ∉ realizableSyndromes P Q) : Module.finrank ℂ (sector P Q horth s) = 0 := by sorry
