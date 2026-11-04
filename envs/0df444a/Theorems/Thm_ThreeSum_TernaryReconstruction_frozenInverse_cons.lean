-- Prove2me | Theorems.Thm_ThreeSum_TernaryReconstruction_frozenInverse_cons
-- name    : ThreeSum.TernaryReconstruction.frozenInverse_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:02.375779+00:00
-- url     : https://prove2.me/theorems/09fc8aab-55e2-42ba-8d22-67ace0d8fabf
-- title:
--   Ternary Reconstruction: frozen Inverse cons
-- statement:
--   The coefficient is attached to a complete lower digit, once per coordinate.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean#L99-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean#L99-L103

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler

theorem ThreeSum.TernaryReconstruction.frozenInverse_cons {N : ℕ} (i : Fin N) (rest : List (Fin N))
    (H : TritWord N → ℤ) (R : TritWord N) :
    frozenInverse (i :: rest) H R = ∑ d : Fin 3, inverseCoefficient (R i) d *
      frozenInverse rest H (Function.update R i d) := by sorry
