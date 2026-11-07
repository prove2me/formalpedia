-- Prove2me | Theorems.Thm_QEC_Coding_CSSDaviesLocality_weightedJump_supported
-- name    : QEC.Coding.CSSDaviesLocality.weightedJump_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:41:47.209132+00:00
-- url     : https://prove2.me/theorems/4041a043-b805-40c2-8d5e-114d9b1013c0
-- title:
--   CSSDavies Locality: weighted Jump supported
-- statement:
--   The CSSDavies Locality construction uses the weighted Jump supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L208-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L208-L214

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.CSSDaviesLocality
open Classical PauliSymplectic QEC.Semantics QEC.Locality QEC.Semantics.Davies
open scoped BigOperators
noncomputable section
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι] [Fintype κP] [Fintype κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
variable (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
include horth

theorem QEC.Coding.CSSDaviesLocality.weightedJump_supported
    (rate : (ι × Axis) → HamiltonianFrequency (hamiltonian P Q) (hamiltonian_symmetric P Q) → ℝ)
    (q : ι) (a : Axis) (ω : HamiltonianFrequency (hamiltonian P Q) (hamiltonian_symmetric P Q)) :
    (subsystem P Q q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian P Q) (hamiltonian_symmetric P Q)
        (fun qa : ι × Axis => coupling qa.1 qa.2) rate ((q,a),ω)) := by sorry
