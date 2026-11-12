-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_succ
-- name    : QEC.Coding.BDL26PaidRowsComposition.totalCost_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:32:47.84247+00:00
-- url     : https://prove2.me/theorems/a3fe130e-a6f2-4bb9-80c2-a9590af3a04f
-- title:
--   BDL26 Paid Rows Composition: total Cost succ
-- statement:
--   The BDL26 Paid Rows Composition construction uses the total Cost succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L139-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L139-L146

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26PaidRowsComposition.totalCost_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p (N+1)) :
    totalCost p (N+1) z = totalCost p N z.1+
      jointRowStageCost p N (evaluate p N z.1,z.2)+
        ((materializationCost p N (evaluate p N z.1,z.2)+
          3*Fintype.card (Vertex (StagePresentation p (N+1))) : ℕ) : ℝ≥0∞) := by sorry
