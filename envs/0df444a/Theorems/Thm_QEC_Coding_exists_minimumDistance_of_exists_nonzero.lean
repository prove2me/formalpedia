-- Prove2me | Theorems.Thm_QEC_Coding_exists_minimumDistance_of_exists_nonzero
-- name    : QEC.Coding.exists_minimumDistance_of_exists_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:14:48.805906+00:00
-- url     : https://prove2.me/theorems/cfb37548-bfbe-4070-a310-16f7d8735637
-- title:
--   Coding: exists minimum Distance of exists nonzero
-- statement:
--   A nonzero finite-coordinate linear code has a minimum distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L463-L481
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L463-L481

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x

theorem QEC.Coding.exists_minimumDistance_of_exists_nonzero {F : Type u} {ι : Type v}
    [Field F] [Fintype F] [DecidableEq F] [Fintype ι] (C : LinearCode F ι)
    (hC : ∃ x : Word F ι, x ∈ C.carrier ∧ x ≠ 0) :
    ∃ d : Nat, MinimumDistance C d := by sorry
