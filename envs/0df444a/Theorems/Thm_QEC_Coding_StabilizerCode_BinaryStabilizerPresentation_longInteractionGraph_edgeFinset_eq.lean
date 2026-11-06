-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_longInteractionGraph_edgeFinset_eq
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.longInteractionGraph_edgeFinset_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:34:20.758823+00:00
-- url     : https://prove2.me/theorems/fbf2cd3d-6fc8-4d30-a29d-1befe427cd52
-- title:
--   Binary Stabilizer Presentation: long Interaction Graph edge Finset eq
-- statement:
--   The long-interaction graph has exactly the filtered unordered edge set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L223-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L223-L235

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.longInteractionGraph_edgeFinset_eq
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) :
    (P.longInteractionGraph embedding threshold).edgeFinset =
      P.interactionsAtLengthAtLeast embedding threshold := by sorry
