-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:47:04.42266+00:00
-- url     : https://prove2.me/theorems/1f7069ac-2604-4c95-9fe3-b051afe7048c
-- title:
--   Binary Stabilizer Presentation: sym2 mk mem interactions At Length At Least iff
-- statement:
--   Endpoint-level specification of thresholded fixed-generator interactions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L168-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L168-L175

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) (p q : ι) :
    s(p, q) ∈ P.interactionsAtLengthAtLeast embedding threshold ↔
      p ≠ q ∧
        (∃ j : κ, p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) ∧
        threshold ≤ embedding.distance p q := by sorry
