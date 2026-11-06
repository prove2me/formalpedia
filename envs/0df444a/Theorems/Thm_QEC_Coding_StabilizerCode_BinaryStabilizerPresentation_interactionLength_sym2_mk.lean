-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:47:07.382163+00:00
-- url     : https://prove2.me/theorems/c085f6ca-1e4c-464e-b888-05ad24269ce5
-- title:
--   Binary Stabilizer Presentation: interaction Length sym2 mk
-- statement:
--   Interaction length on an explicit pair is ordinary Euclidean distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L130-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L130-L133

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (p q : ι) :
    interactionLength embedding s(p, q) = embedding.distance p q := by sorry

attribute [defeq] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
