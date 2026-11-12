-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_zero_seed_davies
-- name    : QEC.Coding.BDL26NativeDaviesLocality.zero_seed_davies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:48:31.255414+00:00
-- url     : https://prove2.me/theorems/f10406c1-7ac6-4cf4-a0bc-233fac9b78fe
-- title:
--   BDL26 Native Davies Locality: zero seed davies
-- statement:
--   The BDL26 Native Davies Locality construction uses the zero seed davies property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L190-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L190-L198

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

theorem QEC.Coding.BDL26NativeDaviesLocality.zero_seed_davies {L : ℝ} (p : GeometricParameters L)
    (z : BDL26NativeFiniteComposition.Experiment p 0) :
    BDL26NativeFiniteComposition.evaluate p 0 z =
      BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) ∧
    BDL26NativeFiniteComposition.totalCost p 0 z = 0 ∧
    DaviesGeometry (perturbationOddScale p) 0
      (BDL26NativeFiniteComposition.evaluate p 0 z) p.t := by sorry
