-- Prove2me | Theorems.Thm_TongEM_wave_equation_B
-- name    : TongEM.wave_equation_B
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T01:34:19.963617+00:00
-- url     : https://prove2.me/theorems/a32ee92f-0871-47fc-afbc-74c4eab6234e
-- title:
--   The magnetic field obeys the wave equation, $\frac{1}{c^2}\partial_t^2B-\nabla^2B=0$
-- statement:
--   Under the same hypotheses as for the electric field — $\mu_0,\varepsilon_0>0$, $c=\sqrt{1/(\mu_0\varepsilon_0)}$, and $E$, $B$ smooth jointly in time and position solving the Maxwell equations in vacuum — the magnetic field satisfies the wave equation
--   $$\frac{1}{c^2}\frac{\partial^2B}{\partial t^2}-\nabla^2B=0$$
--   at every time and every point, with the Laplacian acting componentwise. This is equation (4.14) of Tong's lectures: the magnetic waves travel at the same speed $c$ as the electric ones.
-- source:
--   David Tong, Lectures on Electromagnetism, University of Cambridge Mathematical Tripos Part IB, Lent Term 2015, http://www.damtp.cam.ac.uk/user/tong/em.html — Section 4.3 "And There Was Light", pp. 82–86, equation (4.14)

import Definitions.Def_TongEM_wave_ops

namespace TongEM

open Larmor

theorem wave_equation_B (mu0 eps0 c : ℝ) (hmu0 : 0 < mu0) (heps0 : 0 < eps0)
    (hc : c = Real.sqrt (1 / (mu0 * eps0))) (E B : ℝ → Vec → Vec)
    (hE : SmoothTV E) (hB : SmoothTV B)
    (hEB : IsMaxwell eps0 c (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : Vec)) E B)
    (t : ℝ) (x : Vec) :
    (1 / c ^ 2) • dtt B t x - lapVec (B t) x = 0 := by sorry

end TongEM
