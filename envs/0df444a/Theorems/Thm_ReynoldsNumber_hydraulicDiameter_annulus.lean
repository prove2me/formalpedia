-- Prove2me | Theorems.Thm_ReynoldsNumber_hydraulicDiameter_annulus
-- name    : ReynoldsNumber.hydraulicDiameter_annulus
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T19:22:32.969961+00:00
-- url     : https://prove2.me/theorems/ed3e0e5f-4244-4d25-af0c-ea20bfb89df9
-- title:
--   Annular duct: $D_H = D_o - D_i$
-- statement:
--   For an annular duct — the channel between an outer pipe of inside diameter $D_o$ and an inner pipe of outside diameter $D_i$, with $0<D_i<D_o$ — the cross-sectional area is $A=\pi(D_o^{2}-D_i^{2})/4$ and the wetted perimeter is $P=\pi(D_o+D_i)$. The hydraulic diameter then reduces algebraically to
--   $$D_H=\frac{4A}{P}=D_o-D_i.$$
-- source:
--   Wikipedia, “Reynolds number” (uploaded PDF, Reynolds_number.pdf), sections “Definition”, “Derivation”, “Alternative derivation”, “Flow in a pipe”: https://en.wikipedia.org/wiki/Reynolds_number

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ReynoldsNumber_core

namespace ReynoldsNumber

theorem hydraulicDiameter_annulus (Do Di A P : ℝ) (hDi : 0 < Di) (hDo : Di < Do)
    (hA : A = Real.pi * (Do ^ 2 - Di ^ 2) / 4) (hP : P = Real.pi * (Do + Di)) :
    hydraulicDiameter A P = Do - Di := by sorry

end ReynoldsNumber
