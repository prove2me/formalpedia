-- Prove2me | Theorems.Thm_P2M_SPP_le_s__81aa0fe3ef1b
-- name    : P2M_SPP_le_s__81aa0fe3ef1b
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:07:59.620989+00:00
-- url     : https://prove2.me/theorems/24f3b376-04af-45cd-9744-2375bd8cbf9f
-- title:
--   P2 M SPP le s  81aa0fe3ef1b: P2 M SPP le s  81aa0fe3ef1b
-- statement:
--   The P2 M SPP le s  81aa0fe3ef1b construction uses the P2 M SPP le s  81aa0fe3ef1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L388-L390
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L388-L390

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

theorem P2M_SPP_le_s__81aa0fe3ef1b {s : ℕ} {a : (ZMod n)ˣ} (hs : s < val₂ (n - 1))
    (ha : a ^ (2 ^ s * oddPart (n - 1)) = -1) : s ≤ s₀ n := by sorry

alias «SPP».«le_s₀» := P2M_SPP_le_s__81aa0fe3ef1b
