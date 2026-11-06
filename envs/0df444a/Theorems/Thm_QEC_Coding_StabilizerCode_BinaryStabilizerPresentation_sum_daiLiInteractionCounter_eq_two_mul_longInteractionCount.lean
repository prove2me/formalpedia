-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:00:42.611764+00:00
-- url     : https://prove2.me/theorems/2097dacd-f95e-497c-9c19-a2bcd7a9e8a8
-- title:
--   Binary Stabilizer Presentation: sum dai Li Interaction Counter eq two mul long Interaction Count
-- statement:
--   The total Dai--Li incidence counter is twice the distinct unordered long-edge count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L261-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L261-L284

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) :
    (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) =
      2 * P.longInteractionCount embedding threshold := by sorry
