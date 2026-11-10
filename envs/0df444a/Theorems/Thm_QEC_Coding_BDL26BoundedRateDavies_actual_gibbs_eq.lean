-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_actual_gibbs_eq
-- name    : QEC.Coding.BDL26BoundedRateDavies.actual_gibbs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:31:05.557403+00:00
-- url     : https://prove2.me/theorems/31a8e6f6-e286-49b3-8a85-1f9149a4a884
-- title:
--   BDL26 Bounded Rate Davies: actual gibbs eq
-- statement:
--   The physical family Gibbs state uses this same literal Hamiltonian.
--   The independently proved symmetry witnesses are propositionally irrelevant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L102-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean#L102-L105

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26BoundedRateDavies.actual_gibbs_eq (β : ℝ) :
    (BDL26CSSHamiltonian.gibbs S n β).toOperator =
      (hamiltonianGibbs (BDL26CSSHamiltonian.hamiltonian S n)
        (hamiltonian_symmetric S n) β).toOperator := by sorry
