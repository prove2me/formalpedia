-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_finite_history_davies_ae
-- name    : QEC.Coding.BDL26NativeDaviesLocality.finite_history_davies_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T12:29:09.833587+00:00
-- url     : https://prove2.me/theorems/733b8e25-83dd-42d5-8e81-9e5808d157de
-- title:
--   BDL26 Native Davies Locality: finite history davies ae
-- statement:
--   The BDL26 Native Davies Locality construction uses the finite history davies ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L159-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L159-L164

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

theorem QEC.Coding.BDL26NativeDaviesLocality.finite_history_davies_ae {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p N, ∀ i : Fin (N+1),
      DaviesGeometry (perturbationOddScale p) i.val
        (BDL26NativeFiniteComposition.history p N z i) p.t := by sorry
