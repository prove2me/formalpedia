-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_syndrome_resolution
-- name    : QEC.Coding.CSSGibbs.hamiltonian_syndrome_resolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:06:44.734029+00:00
-- url     : https://prove2.me/theorems/87a5a8f1-4e1f-4bca-a40a-55a0c68cc34a
-- title:
--   CSSGibbs: hamiltonian syndrome resolution
-- statement:
--   A literal syndrome energy decomposition; energy-degenerate sectors remain distinct.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L204-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean#L204-L209

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

theorem QEC.Coding.CSSGibbs.hamiltonian_syndrome_resolution : hamiltonian P Q =
    ∑ s, (energy P Q s : ℂ) • projector P Q horth s := by sorry
