-- Prove2me | Theorems.Thm_SecondLawThermo_work_two_reservoirs
-- name    : SecondLawThermo.work_two_reservoirs
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-15T20:33:19.681305+00:00
-- url     : https://prove2.me/theorems/8b3703b7-840b-4780-aeee-169b22b17c18
-- title:
--   Two-reservoir work identity for thermodynamic cycles
-- statement:
--   Source-faithful helper for the Carnot heat-ratio composition law: a thermodynamic cycle operating only between reservoirs h and k (with k < h) delivers work equal to the sum of its heat exchanges at h and k.
-- source:
--   mission:cfeb14ae-5258-474a-b322-a36986b26451:parent:4dbf97e8-5e63-4b52-a433-eb10a21058cb:E150-declaration

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

open SecondLawThermo

theorem SecondLawThermo.work_two_reservoirs {Θ : Type*} [LinearOrder Θ]
    (c : SecondLawThermo.Cycle Θ) (h k : Θ) (hkh : k < h)
    (hbetween : SecondLawThermo.OperatesBetween c h k) :
    SecondLawThermo.work c = c h + c k := by sorry
