-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_hamiltonian_sector_energy
-- name    : QEC.Coding.BDL26CSSHamiltonian.hamiltonian_sector_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:21:12.102277+00:00
-- url     : https://prove2.me/theorems/0e01c66b-7ae1-4b87-ad69-7adff4f7d82c
-- title:
--   BDL26 CSSHamiltonian: hamiltonian sector energy
-- statement:
--   The BDL26 CSSHamiltonian construction uses the hamiltonian sector energy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L57-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L57-L65

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

theorem QEC.Coding.BDL26CSSHamiltonian.hamiltonian_sector_energy (u : Word (ZMod 2) (ZLabel S n))
    (v : Word (ZMod 2) (XLabel S n)) :
    hamiltonian S n * projector S n (CSSGibbs.joinSyndrome u v) =
      ((-((Fintype.card (ZLabel S n) + Fintype.card (XLabel S n) : Nat) : ℝ) +
        2 * ((HammingWeight u : ℝ) + HammingWeight v) : ℝ) : ℂ) •
        projector S n (CSSGibbs.joinSyndrome u v) := by sorry
