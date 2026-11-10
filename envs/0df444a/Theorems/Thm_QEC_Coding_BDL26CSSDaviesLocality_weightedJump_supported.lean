-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_weightedJump_supported
-- name    : QEC.Coding.BDL26CSSDaviesLocality.weightedJump_supported
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:22:03.14369+00:00
-- url     : https://prove2.me/theorems/6858dbd1-6124-4b8e-aa10-24c437ce5f7b
-- title:
--   BDL26 CSSDavies Locality: weighted Jump supported
-- statement:
--   Algebraic support needs no positivity or detailed-balance assumption on rates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L167-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L167-L173

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_weightedJump_supported
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.weightedJump_supported (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    (subsystem S n q).OperatorSupportedOnRegister
      (hamiltonianJump (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω)) := by sorry
