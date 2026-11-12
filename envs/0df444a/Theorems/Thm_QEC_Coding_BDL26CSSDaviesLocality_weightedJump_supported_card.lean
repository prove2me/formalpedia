-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_weightedJump_supported_card
-- name    : QEC.Coding.BDL26CSSDaviesLocality.weightedJump_supported_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:40:47.008031+00:00
-- url     : https://prove2.me/theorems/a11bc948-8855-4e35-b31b-240eebae5d24
-- title:
--   BDL26 CSSDavies Locality: weighted Jump supported card
-- statement:
--   The BDL26 CSSDavies Locality construction uses the weighted Jump supported card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L181-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L181-L187

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.weightedJump_supported_card (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    (subsystem S n q).OperatorSupportedOnRegister
      (hamiltonianJump (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω)) ∧
      (subsystem S n q).selected.card ≤ 50 := by sorry
