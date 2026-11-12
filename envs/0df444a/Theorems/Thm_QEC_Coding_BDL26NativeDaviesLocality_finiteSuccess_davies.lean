-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_finiteSuccess_davies
-- name    : QEC.Coding.BDL26NativeDaviesLocality.finiteSuccess_davies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:56:51.320467+00:00
-- url     : https://prove2.me/theorems/015a0f22-03ad-430a-9ce8-16a8bfd89335
-- title:
--   BDL26 Native Davies Locality: finite Success davies
-- statement:
--   The BDL26 Native Davies Locality construction uses the finite Success davies property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L150-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L150-L157

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

theorem QEC.Coding.BDL26NativeDaviesLocality.finiteSuccess_davies {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    {z : BDL26NativeFiniteComposition.Experiment p N}
    (hz : z ∈ BDL26NativeFiniteComposition.finiteSuccess p N) :
    ∀ i : Fin (N+1), DaviesGeometry (perturbationOddScale p) i.val
      (BDL26NativeFiniteComposition.history p N z i) p.t := by sorry
