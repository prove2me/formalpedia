-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_reads_rename
-- name    : QEC.Coding.BDL26ReplacementMaterialization.PointCode.reads_rename
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:04:18.430977+00:00
-- url     : https://prove2.me/theorems/ec73e75a-06b7-45c5-9684-49b1724c2891
-- title:
--   Point Code: reads rename
-- statement:
--   The Point Code construction uses the reads rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L113-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L113-L114

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
open QEC.Coding.BDL26ReplacementMaterialization.PointCode
variable {A B : Type*}

theorem QEC.Coding.BDL26ReplacementMaterialization.PointCode.reads_rename (f : A → B) (c : PointCode A) : (c.rename f).reads = c.reads := by sorry
