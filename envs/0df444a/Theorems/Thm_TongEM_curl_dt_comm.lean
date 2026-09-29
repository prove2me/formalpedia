-- Prove2me | Theorems.Thm_TongEM_curl_dt_comm
-- name    : TongEM.curl_dt_comm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T01:29:35.44064+00:00
-- url     : https://prove2.me/theorems/73185832-86be-4640-807c-a060a5c3750b
-- title:
--   The time derivative commutes with the curl
-- statement:
--   Let $F(t,x)$ be a vector field on space depending on time, smooth ($C^\infty$) jointly in time and position. Then differentiating in time and taking the curl may be exchanged: at every time $t$ and point $x$,
--   $$\frac{\partial}{\partial t}\bigl(\nabla\times F\bigr)(t,x)=\nabla\times\Bigl(\frac{\partial F}{\partial t}\Bigr)(t,x).$$
--   On the left the curl is taken at each fixed time and the resulting curve is differentiated in $t$; on the right the field is differentiated in $t$ at each fixed point and the curl of the resulting field is taken.
--
--   This exchange is used silently in the textbook derivation, when $\partial_t(\nabla\times B)$ is rewritten as $\nabla\times(\partial_tB)$.
-- source:
--   David Tong, Lectures on Electromagnetism, University of Cambridge Mathematical Tripos Part IB, Lent Term 2015, http://www.damtp.cam.ac.uk/user/tong/em.html — Section 4.3 "And There Was Light", pp. 82–86, equation (4.12) (the step $\partial_t(\nabla\times B)=\nabla\times\partial_t B$)

import Definitions.Def_TongEM_wave_ops

namespace TongEM

open Larmor

theorem curl_dt_comm (F : ℝ → Vec → Vec) (hF : SmoothTV F) (t : ℝ) (x : Vec) :
    deriv (fun s => curl (F s) x) t = curl (fun y => deriv (fun s => F s y) t) x := by sorry

end TongEM
