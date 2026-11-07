-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiGoodExteriorNeighbors_iff
-- name    : QEC.Locality.mem_daiLiGoodExteriorNeighbors_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:08:15.731854+00:00
-- url     : https://prove2.me/theorems/3545c3a2-dc01-4612-b49e-11c64590e6f6
-- title:
--   Locality: mem dai Li Good Exterior Neighbors iff
-- statement:
--   The Locality construction uses the mem dai Li Good Exterior Neighbors iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1648-L1654
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1648-L1654

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.mem_daiLiGoodExteriorNeighbors_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι) (q : ι) :
    q ∈ daiLiGoodExteriorNeighbors P embedding ell region ↔
      q ∉ region ∧ ∃ p : ι, p ∈ region ∧ P.fixedGeneratorInteraction p q ∧
        embedding.distance p q < ell := by sorry
