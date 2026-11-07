-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_gibbs_bad_trace
-- name    : QEC.Coding.CSSGibbs.gibbs_bad_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:41:29.484506+00:00
-- url     : https://prove2.me/theorems/522a5e8f-3029-43a6-a5d6-b92065667367
-- title:
--   CSSGibbs: gibbs bad trace
-- statement:
--   The CSSGibbs construction uses the gibbs bad trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean#L235-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean#L235-L238

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

theorem QEC.Coding.CSSGibbs.gibbs_bad_trace (β : ℝ) (B : Finset (Word (ZMod 2) (Sum κP κQ))) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι) ((gibbs P Q β).toOperator * badProjector P Q horth B) =
      ((∑ s ∈ B, jointProbability P Q β s : ℝ) : ℂ) := by sorry
