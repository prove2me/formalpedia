-- Prove2me | Theorems.Thm_SPP_G_lt_F_of_not_isPrimePow
-- name    : SPP.G_lt_F_of_not_isPrimePow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:08:18.145544+00:00
-- url     : https://prove2.me/theorems/7f5524b2-0bd2-4ec1-9588-97793fd75164
-- title:
--   SPP: G lt F of not is Prime Pow
-- statement:
--   The SPP construction uses the G lt F of not is Prime Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L416-L452
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L416-L452

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}

theorem SPP.G_lt_F_of_not_isPrimePow [hn : Fact (1 < n)] (ho : Odd n) (hnp : ¬IsPrimePow n) :
    G n < F n := by sorry
