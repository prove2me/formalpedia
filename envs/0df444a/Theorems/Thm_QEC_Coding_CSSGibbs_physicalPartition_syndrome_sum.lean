-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_physicalPartition_syndrome_sum
-- name    : QEC.Coding.CSSGibbs.physicalPartition_syndrome_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:28:17.361056+00:00
-- url     : https://prove2.me/theorems/2639a25b-10a9-4a86-a301-aaf471cdfbb2
-- title:
--   CSSGibbs: physical Partition syndrome sum
-- statement:
--   The CSSGibbs construction uses the physical Partition syndrome sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean#L107-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean#L107-L127

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
include horth

theorem QEC.Coding.CSSGibbs.physicalPartition_syndrome_sum (β : ℝ) : physicalPartition P Q β =
    multiplicity P Q * ∑ s : Realizable P Q,
      Real.exp (-β * energy P Q (joinSyndrome s.1.val s.2.val)) := by sorry
