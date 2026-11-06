-- Prove2me | Theorems.Thm_QEC_Locality_regionInteractionCounter_mono
-- name    : QEC.Locality.regionInteractionCounter_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:02:39.03319+00:00
-- url     : https://prove2.me/theorems/442d4b56-ef05-4206-8923-1d361056ef46
-- title:
--   Locality: region Interaction Counter mono
-- statement:
--   The actual long-interaction counter is monotone under finite region
--   inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L49-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L49-L57

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

theorem QEC.Locality.regionInteractionCounter_mono
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    {inner outer : Finset ι} (hSubset : inner ⊆ outer) :
    regionInteractionCounter P embedding threshold inner ≤
      regionInteractionCounter P embedding threshold outer := by sorry
