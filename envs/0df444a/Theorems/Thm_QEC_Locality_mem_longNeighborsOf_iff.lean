-- Prove2me | Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
-- name    : QEC.Locality.mem_longNeighborsOf_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:48:55.413857+00:00
-- url     : https://prove2.me/theorems/7a458eae-0729-49fe-a524-91bdc7588687
-- title:
--   Locality: mem long Neighbors Of iff
-- statement:
--   The Locality construction uses the mem long Neighbors Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L100-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L100-L109

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.mem_longNeighborsOf_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) (q : ι) :
    q ∈ longNeighborsOf P embedding threshold region ↔
      ∃ p ∈ region,
        P.fixedGeneratorInteraction p q ∧ threshold ≤ embedding.distance p q := by sorry
