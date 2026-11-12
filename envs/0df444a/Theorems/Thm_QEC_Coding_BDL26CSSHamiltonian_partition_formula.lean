-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_partition_formula
-- name    : QEC.Coding.BDL26CSSHamiltonian.partition_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:53:35.404869+00:00
-- url     : https://prove2.me/theorems/2869e1c2-8cd5-4471-869a-3d5483e997a8
-- title:
--   BDL26 CSSHamiltonian: partition formula
-- statement:
--   The BDL26 CSSHamiltonian construction uses the partition formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L71-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L71-L74

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

theorem QEC.Coding.BDL26CSSHamiltonian.partition_formula (β : ℝ) : physicalPartition S n β =
    multiplicity S n * Real.exp (β * (Fintype.card (ZLabel S n) + Fintype.card (XLabel S n) : Nat)) *
      CSSGibbs.rowPartition (zSyndrome S n) (2 * β) * CSSGibbs.rowPartition (xSyndrome S n) (2 * β) := by sorry
