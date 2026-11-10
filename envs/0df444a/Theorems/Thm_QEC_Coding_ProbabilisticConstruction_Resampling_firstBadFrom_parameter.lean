-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_firstBadFrom_parameter
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:32:40.767535+00:00
-- url     : https://prove2.me/theorems/2326de1b-0c60-4841-9408-4dc83bde9b66
-- title:
--   Resampling: first Bad From parameter
-- statement:
--   Carrying the parameter in the sample does not change the selected label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L20-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L20-L28

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
variable {A W I : Type*} [MeasurableSpace A] [MeasurableSpace W]
variable [Fintype I] [LinearOrder I] [MeasurableSpace I]
variable (B : A → I → Set W) [∀ a i, DecidablePred (· ∈ B a i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_parameter (L : List I) (a : A) (w : W) :
    firstBadFrom (B a) L w =
      firstBadFrom (fun i => {z : A × W | z.2 ∈ B z.1 i}) L (a,w) := by sorry
