-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_fixed_parameters_paid_materialization
-- name    : QEC.Coding.BDL26ReplacementMaterialization.fixed_parameters_paid_materialization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T06:51:27.033138+00:00
-- url     : https://prove2.me/theorems/da7682cf-a6ad-4696-a582-30a783f471bd
-- title:
--   BDL26 Replacement Materialization: fixed parameters paid materialization
-- statement:
--   Fixed parameters precede every prefix; rank/setup and incoming-oracle costs remain excluded.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L763-L773
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L763-L773

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26ReplacementMaterialization.fixed_parameters_paid_materialization (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N,
      Measurable (extendedTotalCost p N) ∧
      (∫⁻ z, extendedTotalCost p N z ∂experimentLaw p N) ≤
        (((operationConstant ((6*p.m+2)*p.lambda)*65^10+65536*65^2)*
          (stageQubits p N+1)^11 : ℕ) : ℝ≥0∞) ∧
      ∀ᵐ z ∂experimentLaw p N, z ∈ finiteSuccess p N ∧ extendedTotalCost p N z < ∞ := by sorry
