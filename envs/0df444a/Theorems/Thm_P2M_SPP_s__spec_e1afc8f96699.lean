-- Prove2me | Theorems.Thm_P2M_SPP_s__spec_e1afc8f96699
-- name    : P2M_SPP_s__spec_e1afc8f96699
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:04:05.570653+00:00
-- url     : https://prove2.me/theorems/d8b7cae2-c36d-4e50-beb7-aa175490b6a1
-- title:
--   P2 M SPP s  spec e1afc8f96699: P2 M SPP s  spec e1afc8f96699
-- statement:
--   The P2 M SPP s  spec e1afc8f96699 construction uses the P2 M SPP s  spec e1afc8f96699 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L376-L379
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L376-L379

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

theorem P2M_SPP_s__spec_e1afc8f96699 (n) [Fact (1 < n)] : ∃ a : (ZMod n)ˣ, a ^ (2 ^ s₀ n * oddPart (n - 1)) = -1 := by sorry

alias «SPP».«s₀_spec» := P2M_SPP_s__spec_e1afc8f96699
