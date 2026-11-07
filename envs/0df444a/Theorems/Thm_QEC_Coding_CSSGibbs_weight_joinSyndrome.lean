-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_weight_joinSyndrome
-- name    : QEC.Coding.CSSGibbs.weight_joinSyndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:05:42.834362+00:00
-- url     : https://prove2.me/theorems/f91620d6-8b82-448f-a4a0-e924c59cfd91
-- title:
--   CSSGibbs: weight join Syndrome
-- statement:
--   The CSSGibbs construction uses the weight join Syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L211-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L211-L215

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

theorem QEC.Coding.CSSGibbs.weight_joinSyndrome (u : Word (ZMod 2) κP) (v : Word (ZMod 2) κQ) :
    HammingWeight (joinSyndrome u v) = HammingWeight u + HammingWeight v := by sorry
