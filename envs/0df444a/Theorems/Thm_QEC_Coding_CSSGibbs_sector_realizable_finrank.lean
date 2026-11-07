-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_sector_realizable_finrank
-- name    : QEC.Coding.CSSGibbs.sector_realizable_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:04:57.450227+00:00
-- url     : https://prove2.me/theorems/e865dfbc-9e12-4e53-9f8a-255f2b4bfcf5
-- title:
--   CSSGibbs: sector realizable finrank
-- statement:
--   The CSSGibbs construction uses the sector realizable finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L55-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L55-L59

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

theorem QEC.Coding.CSSGibbs.sector_realizable_finrank (u : LinearMap.range P) (v : LinearMap.range Q) :
    Module.finrank ℂ (sector P Q horth (joinSyndrome u.val v.val)) = multiplicity P Q := by sorry
