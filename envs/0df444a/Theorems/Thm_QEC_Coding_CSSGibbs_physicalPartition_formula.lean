-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_physicalPartition_formula
-- name    : QEC.Coding.CSSGibbs.physicalPartition_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:28:34.866885+00:00
-- url     : https://prove2.me/theorems/5592936c-92a4-4f90-b127-f74460a505ce
-- title:
--   CSSGibbs: physical Partition formula
-- statement:
--   The factor two is forced by the literal check energies, including redundant rows.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean#L131-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean#L131-L147

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

theorem QEC.Coding.CSSGibbs.physicalPartition_formula (β : ℝ) : physicalPartition P Q β =
    multiplicity P Q * Real.exp (β * (Fintype.card κP + Fintype.card κQ : Nat)) *
      rowPartition P (2 * β) * rowPartition Q (2 * β) := by sorry
