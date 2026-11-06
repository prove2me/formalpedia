-- Prove2me | Theorems.Thm_QEC_Coding_exists_relativeMinimumDistance_of_exists_mem_not_mem
-- name    : QEC.Coding.exists_relativeMinimumDistance_of_exists_mem_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:15:00.544707+00:00
-- url     : https://prove2.me/theorems/d2b28eaf-5dcb-4784-89d7-8edb548426f0
-- title:
--   Coding: exists relative Minimum Distance of exists mem not mem
-- statement:
--   A nonempty relative sector of nested finite-coordinate codes has a minimum distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L484-L503
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L484-L503

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x

theorem QEC.Coding.exists_relativeMinimumDistance_of_exists_mem_not_mem
    {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (ambient trivial : LinearCode F ι) (_hsub : trivial.carrier ≤ ambient.carrier)
    (hne : ∃ x : Word F ι, x ∈ ambient.carrier ∧ x ∉ trivial.carrier) :
    ∃ d : Nat, RelativeMinimumDistance ambient trivial d := by sorry
