-- Prove2me | Theorems.Thm_TongEM_em_wave_equation
-- name    : TongEM.em_wave_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T01:37:24.371144+00:00
-- url     : https://prove2.me/theorems/6a4c97af-d3f4-487d-b108-d0bd9e25ddf0
-- title:
--   Maxwell in vacuum implies electromagnetic waves at speed $c=1/\sqrt{\mu_0\varepsilon_0}$
-- statement:
--   **Goal theorem.** Let $\mu_0>0$ and $\varepsilon_0>0$, and set
--   $$c=\sqrt{\frac{1}{\mu_0\varepsilon_0}}.$$
--   Let $E$ and $B$ be vector fields on $\mathbb{R}^3$ depending on time, each smooth jointly in time and position, satisfying the Maxwell equations with no charges and no currents:
--   $$\nabla\cdot E=0,\qquad \nabla\cdot B=0,\qquad \nabla\times E=-\frac{\partial B}{\partial t},\qquad \nabla\times B=\mu_0\varepsilon_0\frac{\partial E}{\partial t}.$$
--   Then both fields satisfy the wave equation with speed $c$: at every time and every point,
--   $$\frac{1}{c^2}\frac{\partial^2E}{\partial t^2}-\nabla^2E=0 \qquad\text{and}\qquad \frac{1}{c^2}\frac{\partial^2B}{\partial t^2}-\nabla^2B=0 .$$
--
--   This is the content of equations (4.13) and (4.14) of Section 4.3 of Tong's lectures: the vacuum Maxwell system forces every component of the electric and of the magnetic field to obey one and the same wave equation, whose propagation speed is determined by the two constants $\mu_0$ and $\varepsilon_0$ measured in static experiments.
-- source:
--   David Tong, Lectures on Electromagnetism, University of Cambridge Mathematical Tripos Part IB, Lent Term 2015, http://www.damtp.cam.ac.uk/user/tong/em.html — Section 4.3 "And There Was Light", pp. 82–86, equations (4.13) and (4.14)

import Definitions.Def_TongEM_wave_ops

namespace TongEM

open Larmor

theorem em_wave_equation (mu0 eps0 c : ℝ) (hmu0 : 0 < mu0) (heps0 : 0 < eps0)
    (hc : c = Real.sqrt (1 / (mu0 * eps0))) (E B : ℝ → Vec → Vec)
    (hE : SmoothTV E) (hB : SmoothTV B)
    (hEB : IsMaxwell eps0 c (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : Vec)) E B)
    (t : ℝ) (x : Vec) :
    box c E t x = 0 ∧ box c B t x = 0 := by sorry

end TongEM
