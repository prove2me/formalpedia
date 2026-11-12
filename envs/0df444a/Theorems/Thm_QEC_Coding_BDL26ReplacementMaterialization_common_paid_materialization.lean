-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_common_paid_materialization
-- name    : QEC.Coding.BDL26ReplacementMaterialization.common_paid_materialization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:50:43.045202+00:00
-- url     : https://prove2.me/theorems/97a8f381-d909-4d23-a208-9449cda21a9a
-- title:
--   BDL26 Replacement Materialization: common paid materialization
-- statement:
--   The BDL26 Replacement Materialization construction uses the common paid materialization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L753-L760
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L753-L760

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

theorem QEC.Coding.BDL26ReplacementMaterialization.common_paid_materialization {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) :
    (∀ N, extendedTotalCost p N (BDL26CountableEmbeddingExperiment.truncate p N omega) < ∞) ∧
    ∀ n, PhysicalGeometry (perturbationOddScale p) n
      (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t := by sorry
