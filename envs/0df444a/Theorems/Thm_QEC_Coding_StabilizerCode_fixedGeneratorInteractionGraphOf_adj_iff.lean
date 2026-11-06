-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_fixedGeneratorInteractionGraphOf_adj_iff
-- name    : QEC.Coding.StabilizerCode.fixedGeneratorInteractionGraphOf_adj_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:42:50.444168+00:00
-- url     : https://prove2.me/theorems/f00e73b0-4061-4ff4-a4db-d28d9ea8d866
-- title:
--   Stabilizer Code: fixed Generator Interaction Graph Of adj iff
-- statement:
--   Family-level adjacency is exactly common actual Pauli support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L48-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L48-L53

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
omit [Fintype κ]

theorem QEC.Coding.StabilizerCode.fixedGeneratorInteractionGraphOf_adj_iff
    (generators : κ → Binary ι) (p q : ι) :
    (fixedGeneratorInteractionGraphOf generators).adjacent p q ↔
      p ≠ q ∧ ∃ j : κ,
        p ∈ support (generators j) ∧ q ∈ support (generators j) := by sorry
