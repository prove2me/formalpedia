-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_source_even_davies
-- name    : QEC.Coding.BDL26NativeDaviesLocality.source_even_davies
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T12:54:45.94333+00:00
-- url     : https://prove2.me/theorems/2ec630bb-9de6-409a-ab17-7ce377dcd49b
-- title:
--   BDL26 Native Davies Locality: source even davies
-- statement:
--   The BDL26 Native Davies Locality construction uses the source even davies property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L228-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L228-L233

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

theorem QEC.Coding.BDL26NativeDaviesLocality.source_even_davies {L : ℝ} (p : GeometricParameters L) (k : ℕ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (2*k),
      DaviesGeometry (perturbationOddScale p) (2*k)
        (BDL26NativeFiniteComposition.evaluate p (2*k) z) p.t := by sorry
