-- Prove2me | Theorems.Thm_QEC_Coding_exists_algebraicCSSMinimumDistance_of_exists_logical
-- name    : QEC.Coding.exists_algebraicCSSMinimumDistance_of_exists_logical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:14:52.095833+00:00
-- url     : https://prove2.me/theorems/dd860299-b6ca-4dd9-a058-a18cff45f9f4
-- title:
--   Coding: exists algebraic CSSMinimum Distance of exists logical
-- statement:
--   Any nonempty union of the two finite CSS logical sectors has an attained
--   algebraic minimum distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L395-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L395-L420

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x

theorem QEC.Coding.exists_algebraicCSSMinimumDistance_of_exists_logical
    {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι]
    (xCode zCode : LinearCode F ι)
    (hne : ∃ x : Word F ι,
      (x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
        (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)) :
    ∃ d : Nat, AlgebraicCSSMinimumDistance xCode zCode d := by sorry
