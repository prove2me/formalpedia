-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionsAtLengthAtLeast_anti_mono
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionsAtLengthAtLeast_anti_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:50:14.090262+00:00
-- url     : https://prove2.me/theorems/7065e9a0-c77e-4754-85b9-2ba585d2a95f
-- title:
--   Binary Stabilizer Presentation: interactions At Length At Least anti mono
-- statement:
--   Raising the length threshold can only remove unordered interactions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L192-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L192-L200

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionsAtLengthAtLeast_anti_mono
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι)
    {low high : ℝ} (hlowhigh : low ≤ high) :
    P.interactionsAtLengthAtLeast embedding high ⊆
      P.interactionsAtLengthAtLeast embedding low := by sorry
