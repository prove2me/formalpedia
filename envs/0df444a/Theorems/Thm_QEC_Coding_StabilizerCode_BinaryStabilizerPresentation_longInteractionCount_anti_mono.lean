-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_longInteractionCount_anti_mono
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.longInteractionCount_anti_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:34:19.727581+00:00
-- url     : https://prove2.me/theorems/536698ec-dcfe-4414-871e-bdd9b0d7fdfb
-- title:
--   Binary Stabilizer Presentation: long Interaction Count anti mono
-- statement:
--   Raising the length threshold cannot increase the unordered-edge count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L203-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L203-L208

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.longInteractionCount_anti_mono
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι)
    {low high : ℝ} (hlowhigh : low ≤ high) :
    P.longInteractionCount embedding high ≤ P.longInteractionCount embedding low := by sorry
