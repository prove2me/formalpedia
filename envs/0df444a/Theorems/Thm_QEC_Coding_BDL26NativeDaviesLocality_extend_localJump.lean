-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_extend_localJump
-- name    : QEC.Coding.BDL26NativeDaviesLocality.extend_localJump
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:28:43.093252+00:00
-- url     : https://prove2.me/theorems/13ca0877-2370-4dca-85b4-29f1328c9686
-- title:
--   BDL26 Native Davies Locality: extend local Jump
-- statement:
--   The BDL26 Native Davies Locality construction uses the extend local Jump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L78-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L78-L85

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

theorem QEC.Coding.BDL26NativeDaviesLocality.extend_localJump (S : OddScale) (n : ℕ)
    (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    (subsystem S n q).extendLocalToRegister (localJump S n rate q a ω) =
      hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
        (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω) := by sorry
