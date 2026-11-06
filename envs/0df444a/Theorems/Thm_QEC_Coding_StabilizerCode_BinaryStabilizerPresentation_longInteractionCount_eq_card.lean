-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_longInteractionCount_eq_card
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.longInteractionCount_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:34:01.763014+00:00
-- url     : https://prove2.me/theorems/ed7b72b1-bae5-479b-98df-33ec84c3e404
-- title:
--   Binary Stabilizer Presentation: long Interaction Count eq card
-- statement:
--   The count is definitionally the finite cardinality, never supplied data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L184-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L184-L189

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.longInteractionCount_eq_card
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) :
    P.longInteractionCount embedding threshold =
      (P.interactionsAtLengthAtLeast embedding threshold).card := by sorry
