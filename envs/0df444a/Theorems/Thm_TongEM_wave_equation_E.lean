-- Prove2me | Theorems.Thm_TongEM_wave_equation_E
-- name    : TongEM.wave_equation_E
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T01:30:31.894873+00:00
-- url     : https://prove2.me/theorems/0eae926c-338b-4b13-885f-352e1865bb7d
-- title:
--   The electric field obeys the wave equation, $\frac{1}{c^2}\partial_t^2E-\nabla^2E=0$
-- statement:
--   Let $\mu_0>0$ and $\varepsilon_0>0$ be the magnetic and electric constants and put $c=\sqrt{1/(\mu_0\varepsilon_0)}$, so that $\mu_0\varepsilon_0=1/c^2$. Let $E$ and $B$ be vector fields on space depending on time, each smooth jointly in time and position, satisfying the Maxwell equations in vacuum, that is with vanishing charge density and vanishing current density:
--   $$\nabla\cdot E=0,\qquad \nabla\cdot B=0,\qquad \nabla\times E=-\frac{\partial B}{\partial t},\qquad \nabla\times B=\mu_0\varepsilon_0\frac{\partial E}{\partial t}.$$
--   Then at every time and every point the electric field satisfies the wave equation
--   $$\frac{1}{c^2}\frac{\partial^2E}{\partial t^2}-\nabla^2E=0,$$
--   the Laplacian acting componentwise. This is equation (4.13) of Tong's lectures.
-- source:
--   David Tong, Lectures on Electromagnetism, University of Cambridge Mathematical Tripos Part IB, Lent Term 2015, http://www.damtp.cam.ac.uk/user/tong/em.html — Section 4.3 "And There Was Light", pp. 82–86, equation (4.13)

import Definitions.Def_TongEM_wave_ops

namespace TongEM

open Larmor

theorem wave_equation_E (mu0 eps0 c : ℝ) (hmu0 : 0 < mu0) (heps0 : 0 < eps0)
    (hc : c = Real.sqrt (1 / (mu0 * eps0))) (E B : ℝ → Vec → Vec)
    (hE : SmoothTV E) (hB : SmoothTV B)
    (hEB : IsMaxwell eps0 c (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : Vec)) E B)
    (t : ℝ) (x : Vec) :
    (1 / c ^ 2) • dtt E t x - lapVec (E t) x = 0 := by sorry

end TongEM
