-- Prove2me | Theorems.Thm_RH_Transport_Reflected_retained_kernel_quarter
-- name    : RH.Transport.Reflected.retained_kernel_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:27:43.007497+00:00
-- url     : https://prove2.me/theorems/7a722429-10df-404f-8a43-56c80f82e767
-- title:
--   Reflected: retained kernel quarter
-- statement:
--   The Reflected construction uses the retained kernel quarter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/ReflectedExponent.lean#L50-L54
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/ReflectedExponent.lean#L50-L54

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_ReflectedExponent
set_option autoImplicit false
open RH RH.Transport RH.Transport.Reflected
noncomputable section

theorem RH.Transport.Reflected.retained_kernel_quarter (Td y : ℝ) :
    Td / 4 ≤ y / 4 + max 0 (Td - y) / 2 := by sorry
