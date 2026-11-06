-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_daiLiInteractionCounter_eq_neighborFinset_card
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.daiLiInteractionCounter_eq_neighborFinset_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:50:07.3202+00:00
-- url     : https://prove2.me/theorems/57897481-6bda-43d1-b7fa-3e910291df61
-- title:
--   Binary Stabilizer Presentation: dai Li Interaction Counter eq neighbor Finset card
-- statement:
--   Counter membership specification using actual generator support and Euclidean length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L245-L258
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L245-L258

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.daiLiInteractionCounter_eq_neighborFinset_card
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) (q : ι) :
    P.daiLiInteractionCounter embedding threshold q =
      ((Finset.univ.filter fun r : ι =>
        q ≠ r ∧
          (∃ j : κ, q ∈ P.generatorSupport j ∧ r ∈ P.generatorSupport j) ∧
          threshold ≤ embedding.distance q r).card) := by sorry
