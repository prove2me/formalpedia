-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_expansionWitness_of_not_hasStrongSmallSetExpansion
-- name    : QEC.Coding.FiberBundle.RandomBase.exists_expansionWitness_of_not_hasStrongSmallSetExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:47:43.027621+00:00
-- url     : https://prove2.me/theorems/43349d17-3bfc-4107-b105-5874e9a19db5
-- title:
--   Random Base: exists expansion Witness of not has Strong Small Set Expansion
-- statement:
--   Every failed expansion instance produces a finite containment witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L598-L609
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L598-L609

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.exists_expansionWitness_of_not_hasStrongSmallSetExpansion
    {r Delta : Nat} {sample : Sample r}
    (h : ¬HasStrongSmallSetExpansion (Delta := Delta) sample) :
    ∃ witness : ExpansionWitness r Delta,
      AvoidsOutside witness.1.1 witness.1.2 sample := by sorry
