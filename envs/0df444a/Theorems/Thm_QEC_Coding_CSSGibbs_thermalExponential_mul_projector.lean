-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_thermalExponential_mul_projector
-- name    : QEC.Coding.CSSGibbs.thermalExponential_mul_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:27:06.175723+00:00
-- url     : https://prove2.me/theorems/7c715528-c57a-4ed9-b79f-928448cb51c3
-- title:
--   CSSGibbs: thermal Exponential mul projector
-- statement:
--   The CSSGibbs construction uses the thermal Exponential mul projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean#L86-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean#L86-L97

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics Semantics.Davies Semantics.ThermalEncoding
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_28fb820634_14
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_28fb820634_15

theorem QEC.Coding.CSSGibbs.thermalExponential_mul_projector (β : ℝ) (s : Word (ZMod 2) (Sum κP κQ)) :
    thermalExponential P Q β * projector P Q horth s =
      (Real.exp (-β * energy P Q s) : ℂ) • projector P Q horth s := by sorry
