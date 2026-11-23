-- Prove2me | Theorems.Thm_P2M_val__le_of_dvd_8dcb8b84cddb
-- name    : P2M_val__le_of_dvd_8dcb8b84cddb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:46.804978+00:00
-- url     : https://prove2.me/theorems/0f4ae8b3-3866-4fc9-a4f4-4bf3725a5047
-- title:
--   P2 M val  le of dvd 8dcb8b84cddb: P2 M val  le of dvd 8dcb8b84cddb
-- statement:
--   The P2 M val  le of dvd 8dcb8b84cddb construction uses the P2 M val  le of dvd 8dcb8b84cddb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L46-L47
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L46-L47

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
set_option autoImplicit false
open Nat
variable {n : ℕ}
variable {m : ℕ}

theorem P2M_val__le_of_dvd_8dcb8b84cddb [hn : NeZero n] (h : m ∣ n) : val₂ m ≤ val₂ n := by sorry

alias «val₂_le_of_dvd» := P2M_val__le_of_dvd_8dcb8b84cddb
