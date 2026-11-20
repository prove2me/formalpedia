-- Prove2me | Theorems.Thm_Sensitivity_sensitivity_ge_sqrt_degree
-- name    : Sensitivity.sensitivity_ge_sqrt_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T02:57:34.596179+00:00
-- url     : https://prove2.me/theorems/7a7adf97-323d-489e-be71-0d587ff200ef
-- title:
--   Sensitivity: sensitivity ge sqrt degree
-- statement:
--   **Sensitivity Theorem** (Huang 2019).
--       For any Boolean function f of degree d ≥ 1,
--       the sensitivity satisfies s(f) ≥ ⌈√d⌉, i.e., √d ≤ s(f) as reals.
--
--   Source: https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Main.lean#L37-L202
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Main.lean#L37-L202

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
import Definitions.Def_Sensitivity_Parity
import Definitions.Def_Sensitivity_Main
set_option autoImplicit false
open Sensitivity

theorem Sensitivity.sensitivity_ge_sqrt_degree {n : ℕ} (f : BoolFun n) (hd : 1 ≤ f.degree) :
    Real.sqrt (f.degree : ℝ) ≤ (f.sensitivity : ℝ) := by sorry
