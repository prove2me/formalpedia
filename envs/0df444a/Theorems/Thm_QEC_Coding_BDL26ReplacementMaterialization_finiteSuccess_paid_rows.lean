-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_finiteSuccess_paid_rows
-- name    : QEC.Coding.BDL26ReplacementMaterialization.finiteSuccess_paid_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:50:46.362934+00:00
-- url     : https://prove2.me/theorems/4e7b7a58-cc58-4135-a5ac-2845334fc82f
-- title:
--   BDL26 Replacement Materialization: finite Success paid rows
-- statement:
--   The BDL26 Replacement Materialization construction uses the finite Success paid rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L747-L751
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L747-L751

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

theorem QEC.Coding.BDL26ReplacementMaterialization.finiteSuccess_paid_rows {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) (h : z ∈ finiteSuccess p N) (i : Fin N) :
    PhysicalSuccessorFacts p i.val (stageInput p N i z) (tableAt p N i z) ∧
      extendedTotalCost p N z < ∞ := by sorry
