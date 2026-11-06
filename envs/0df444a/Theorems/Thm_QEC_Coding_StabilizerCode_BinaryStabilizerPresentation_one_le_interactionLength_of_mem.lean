-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_one_le_interactionLength_of_mem
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.one_le_interactionLength_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:33:59.2181+00:00
-- url     : https://prove2.me/theorems/5974134a-75c7-42e4-b9b0-6bf77718da00
-- title:
--   Binary Stabilizer Presentation: one le interaction Length of mem
-- statement:
--   Every actual interaction has length at least one in a unit-separated embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L136-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L136-L145

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.one_le_interactionLength_of_mem
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι)
    {edge : Sym2 ι} (hedge : edge ∈ P.fixedGeneratorInteractions) :
    1 ≤ interactionLength embedding edge := by sorry
