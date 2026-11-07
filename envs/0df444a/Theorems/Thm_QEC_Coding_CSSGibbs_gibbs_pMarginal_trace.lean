-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_gibbs_pMarginal_trace
-- name    : QEC.Coding.CSSGibbs.gibbs_pMarginal_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:41:53.660428+00:00
-- url     : https://prove2.me/theorems/be20bbc3-d6e4-4db0-94d8-896b03406c4c
-- title:
--   CSSGibbs: gibbs p Marginal trace
-- statement:
--   The CSSGibbs construction uses the gibbs p Marginal trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean#L248-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean#L248-L254

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

theorem QEC.Coding.CSSGibbs.gibbs_pMarginal_trace (β : ℝ) (u : LinearMap.range P) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι)
      ((gibbs P Q β).toOperator * pMarginalProjector P Q horth u) =
      (rowProbability P (2 * β) u : ℂ) := by sorry
