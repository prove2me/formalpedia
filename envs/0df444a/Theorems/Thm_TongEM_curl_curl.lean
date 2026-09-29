-- Prove2me | Theorems.Thm_TongEM_curl_curl
-- name    : TongEM.curl_curl
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T01:19:09.077294+00:00
-- url     : https://prove2.me/theorems/af6937bb-fffd-4170-8aa0-0ff5d47befdf
-- title:
--   $\nabla\times(\nabla\times F)=\nabla(\nabla\cdot F)-\nabla^2F$
-- statement:
--   Let $F:\mathbb{R}^3\to\mathbb{R}^3$ be a smooth ($C^\infty$) vector field on space. Then at every point
--   $$\nabla\times(\nabla\times F)=\nabla(\nabla\cdot F)-\nabla^2F,$$
--   where $\nabla\cdot F=\sum_i\partial_iF_i$ is the divergence, $\nabla\times F$ is the curl with components $(\partial_1F_2-\partial_2F_1,\ \partial_2F_0-\partial_0F_2,\ \partial_0F_1-\partial_1F_0)$, $\nabla$ applied to a scalar is the gradient, and the Laplacian of a vector field acts componentwise.
--
--   This is equation (4.12) of Tong's lectures, the identity that turns the pair of curl equations of the vacuum Maxwell system into a second-order equation for a single field.
-- source:
--   David Tong, Lectures on Electromagnetism, University of Cambridge Mathematical Tripos Part IB, Lent Term 2015, http://www.damtp.cam.ac.uk/user/tong/em.html — Section 4.3 "And There Was Light", pp. 82–86, equation (4.12)

import Definitions.Def_TongEM_wave_ops

namespace TongEM

open Larmor

theorem curl_curl (F : Vec → Vec) (hF : SmoothV F) (x : Vec) :
    curl (curl F) x = grad (divg F) x - lapVec F x := by sorry

end TongEM
