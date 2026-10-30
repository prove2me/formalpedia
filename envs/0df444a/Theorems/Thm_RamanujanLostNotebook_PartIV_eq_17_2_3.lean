-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_eq_17_2_3
-- name    : RamanujanLostNotebook.PartIV.eq_17_2_3
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T12:47:47.968328+00:00
-- url     : https://prove2.me/theorems/cac23b73-8d54-4a26-9682-5eea3c7928da
-- title:
--   Fourier sine series for Phi(tan x) - x log tan x
-- statement:
--   With $\Phi(x)=\int_0^x \frac{\arctan t}{t}\,dt$: for $0<x<\pi/2$, $\sum_{n\ge0}\frac{\sin((4n+2)x)}{(2n+1)^2}=\Phi(\tan x)-x\log\tan x$.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 17, Entry 17.2.3, p. 362, eq. (17.2.3).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIV_ch17_arctanIntegral

namespace RamanujanLostNotebook.PartIV
theorem eq_17_2_3 (x : ℝ) (hx0 : 0 < x) (hx1 : x < Real.pi / 2) :
    HasSum (fun n : ℕ => Real.sin ((4 * (n : ℝ) + 2) * x) / (2 * (n : ℝ) + 1) ^ 2)
      (arctanIntegral (Real.tan x) - x * Real.log (Real.tan x)) := by sorry
end RamanujanLostNotebook.PartIV
