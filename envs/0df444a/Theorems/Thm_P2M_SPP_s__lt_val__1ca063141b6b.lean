-- Prove2me | Theorems.Thm_P2M_SPP_s__lt_val__1ca063141b6b
-- name    : P2M_SPP_s__lt_val__1ca063141b6b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:03:50.024165+00:00
-- url     : https://prove2.me/theorems/90516d7a-a92a-48c0-823b-f656211aa7ae
-- title:
--   P2 M SPP s  lt val  1ca063141b6b: P2 M SPP s  lt val  1ca063141b6b
-- statement:
--   The P2 M SPP s  lt val  1ca063141b6b construction uses the P2 M SPP s  lt val  1ca063141b6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L373-L374
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L373-L374

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

theorem P2M_SPP_s__lt_val__1ca063141b6b [Fact (1 < n)] (ho : Odd n) : s₀ n < val₂ (n - 1) := by sorry

alias «SPP».«s₀_lt_val₂» := P2M_SPP_s__lt_val__1ca063141b6b
