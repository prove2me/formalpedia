-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_projector_eq_zero_of_not_realizable
-- name    : QEC.Coding.CSSGibbs.projector_eq_zero_of_not_realizable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:04:56.85385+00:00
-- url     : https://prove2.me/theorems/fd1cbe41-9c70-482e-b425-9bc39e991631
-- title:
--   CSSGibbs: projector eq zero of not realizable
-- statement:
--   Completeness and the derived dimension count exclude every impossible sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L120-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L120-L132

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

theorem QEC.Coding.CSSGibbs.projector_eq_zero_of_not_realizable (s : Word (ZMod 2) (Sum κP κQ))
    (hs : s ∉ realizableSyndromes P Q) : projector P Q horth s = 0 := by sorry
