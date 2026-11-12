-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_finiteDaviesSuccess_eq
-- name    : QEC.Coding.BDL26NativeDaviesLocality.finiteDaviesSuccess_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:08:37.098179+00:00
-- url     : https://prove2.me/theorems/07bfc2b4-227e-40ac-8f5f-465f6987ce0d
-- title:
--   BDL26 Native Davies Locality: finite Davies Success eq
-- statement:
--   The BDL26 Native Davies Locality construction uses the finite Davies Success eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L173-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L173-L178

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
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

theorem QEC.Coding.BDL26NativeDaviesLocality.finiteDaviesSuccess_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    finiteDaviesSuccess p N = BDL26NativeFiniteComposition.finiteSuccess p N := by sorry
