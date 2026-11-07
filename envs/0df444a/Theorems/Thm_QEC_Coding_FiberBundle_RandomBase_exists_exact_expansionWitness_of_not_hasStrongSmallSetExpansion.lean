-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_exact_expansionWitness_of_not_hasStrongSmallSetExpansion
-- name    : QEC.Coding.FiberBundle.RandomBase.exists_exact_expansionWitness_of_not_hasStrongSmallSetExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:18.730826+00:00
-- url     : https://prove2.me/theorems/afaafed2-344e-438b-bab1-e36ff864b647
-- title:
--   Random Base: exists exact expansion Witness of not has Strong Small Set Expansion
-- statement:
--   Every failed expansion instance has a witness whose second component is the
--   *actual* variable neighborhood.  Keeping equality here, rather than weakening
--   it to containment, prevents the same sample from being charged to every
--   superset of its neighborhood.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1369-L1378
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1369-L1378

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.exists_exact_expansionWitness_of_not_hasStrongSmallSetExpansion
    {r Delta : Nat} {sample : Sample r}
    (h : ¬HasStrongSmallSetExpansion (Delta := Delta) sample) :
    ∃ witness : ExpansionWitness r Delta,
      checkSetNeighborhood sample witness.1.1 = witness.1.2 := by sorry
