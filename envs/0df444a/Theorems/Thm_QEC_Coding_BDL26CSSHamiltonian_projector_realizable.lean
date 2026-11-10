-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_projector_realizable
-- name    : QEC.Coding.BDL26CSSHamiltonian.projector_realizable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:51:48.168568+00:00
-- url     : https://prove2.me/theorems/9563de6b-4a3a-45d4-b540-47a4ab3cd37b
-- title:
--   BDL26 CSSHamiltonian: projector realizable
-- statement:
--   The BDL26 CSSHamiltonian construction uses the projector realizable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L40-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L40-L44

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25

theorem QEC.Coding.BDL26CSSHamiltonian.projector_realizable (s : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n))) :
    projector S n s ≠ 0 ↔
      (fun z => s (.inl z)) ∈ LinearMap.range (zSyndrome S n) ∧
      (fun x => s (.inr x)) ∈ LinearMap.range (xSyndrome S n) := by sorry
