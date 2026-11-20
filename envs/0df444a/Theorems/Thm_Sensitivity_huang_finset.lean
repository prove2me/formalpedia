-- Prove2me | Theorems.Thm_Sensitivity_huang_finset
-- name    : Sensitivity.huang_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T02:57:10.838434+00:00
-- url     : https://prove2.me/theorems/0eb6e3f1-e48d-48c6-8e28-41f830c8e727
-- title:
--   Sensitivity: huang finset
-- statement:
--   Mathlib's Huang theorem restated with Finsets.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/HuangBridge.lean#L25-L72
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/HuangBridge.lean#L25-L72

import Definitions.Def_Sensitivity_Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.Real.Sqrt
set_option autoImplicit false
open Sensitivity

theorem Sensitivity.huang_finset {m : ℕ} (H : Finset (Fin (m + 1) → Bool))
    (hH : 2 ^ m + 1 ≤ H.card) :
    ∃ q ∈ H, Real.sqrt (↑m + 1) ≤
      ↑(H.filter (fun p => ∃ i, p = flipBit q i)).card := by sorry
