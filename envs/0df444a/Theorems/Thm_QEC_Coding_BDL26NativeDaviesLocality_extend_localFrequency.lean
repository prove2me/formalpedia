-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_extend_localFrequency
-- name    : QEC.Coding.BDL26NativeDaviesLocality.extend_localFrequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:28:16.818047+00:00
-- url     : https://prove2.me/theorems/e179e0d2-5483-4c01-95b1-6ca391cf021f
-- title:
--   BDL26 Native Davies Locality: extend local Frequency
-- statement:
--   True identity extension of the canonical restriction on the unchanged region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L61-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L61-L67

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeDaviesLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open BDL26CSSDaviesLocality
open PauliSymplectic Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26NativeDaviesLocality.extend_localFrequency (S : OddScale) (n : ℕ) (q : Physical S n)
    (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (subsystem S n q).extendLocalToRegister (localFrequency S n q a ω) =
      actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω := by sorry
