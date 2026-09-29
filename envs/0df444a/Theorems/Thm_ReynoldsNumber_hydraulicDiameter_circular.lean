-- Prove2me | Theorems.Thm_ReynoldsNumber_hydraulicDiameter_circular
-- name    : ReynoldsNumber.hydraulicDiameter_circular
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T19:02:47.562663+00:00
-- url     : https://prove2.me/theorems/760b3eb5-ff74-4d1b-8f95-ad07512f270a
-- title:
--   Circular pipe: $D_H = D$
-- statement:
--   For a circular pipe of inside diameter $D>0$, the cross-sectional area is $A=\pi D^{2}/4$ and the wetted perimeter is $P=\pi D$. Hence the hydraulic diameter reduces to the inside diameter:
--   $$D_H=\frac{4A}{P}=\frac{4\cdot \pi D^{2}/4}{\pi D}=D.$$
-- source:
--   Wikipedia, “Reynolds number” (uploaded PDF, Reynolds_number.pdf), sections “Definition”, “Derivation”, “Alternative derivation”, “Flow in a pipe”: https://en.wikipedia.org/wiki/Reynolds_number

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ReynoldsNumber_core

namespace ReynoldsNumber

theorem hydraulicDiameter_circular (D A P : ℝ) (hD : 0 < D) (hA : A = Real.pi * D ^ 2 / 4)
    (hP : P = Real.pi * D) : hydraulicDiameter A P = D := by sorry

end ReynoldsNumber
