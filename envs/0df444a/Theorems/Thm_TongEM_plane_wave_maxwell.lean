-- Prove2me | Theorems.Thm_TongEM_plane_wave_maxwell
-- name    : TongEM.plane_wave_maxwell
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T01:39:00.40199+00:00
-- url     : https://prove2.me/theorems/5e3c691a-a553-4fb8-b486-cc5bde4a0adc
-- title:
--   The monochromatic plane wave with $\omega=ck$ solves the vacuum Maxwell equations
-- statement:
--   Let $\mu_0,\varepsilon_0>0$, let $c=\sqrt{1/(\mu_0\varepsilon_0)}$, and let $E_0$, $k$, $\omega$ be real numbers subject to the dispersion relation
--   $$\omega=ck.$$
--   Then the fields
--   $$E(t,x)=\bigl(0,\;E_0\sin(kx_0-\omega t),\;0\bigr),\qquad
--   B(t,x)=\Bigl(0,\;0,\;\frac{E_0}{c}\sin(kx_0-\omega t)\Bigr)$$
--   — a wave travelling in the $x$-direction, with the electric field oscillating along $y$ and the magnetic field along $z$ — satisfy the Maxwell equations in vacuum.
--
--   These are equations (4.15) and (4.16) of Tong's lectures. Beyond reproducing the textbook solution, the statement certifies that the hypotheses of the goal theorem are satisfied by non-constant fields, so the mission's main result is not a claim about an empty or trivial class.
-- source:
--   David Tong, Lectures on Electromagnetism, University of Cambridge Mathematical Tripos Part IB, Lent Term 2015, http://www.damtp.cam.ac.uk/user/tong/em.html — Section 4.3 "And There Was Light", pp. 82–86, equations (4.15) and (4.16)

import Definitions.Def_TongEM_wave_ops

namespace TongEM

open Larmor

theorem plane_wave_maxwell (mu0 eps0 c E0 k omega : ℝ) (hmu0 : 0 < mu0) (heps0 : 0 < eps0)
    (hc : c = Real.sqrt (1 / (mu0 * eps0))) (hdisp : omega = c * k) :
    IsMaxwell eps0 c (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : Vec))
      (fun t x => !₂[0, E0 * Real.sin (k * x 0 - omega * t), 0])
      (fun t x => !₂[0, 0, (E0 / c) * Real.sin (k * x 0 - omega * t)]) := by sorry

end TongEM
