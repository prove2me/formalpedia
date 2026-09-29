-- Prove2me | Theorems.Thm_TongEM_pd_comm
-- name    : TongEM.pd_comm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T01:10:27.18872+00:00
-- url     : https://prove2.me/theorems/681e0679-fae9-4a45-9125-bb9a81ddd1e0
-- title:
--   Symmetry of second partial derivatives
-- statement:
--   Let $f:\mathbb{R}^3\to\mathbb{R}$ be a smooth ($C^\infty$) scalar field. Then its second partial derivatives are symmetric: for all coordinate directions $i,j\in\{0,1,2\}$ and every point $x$,
--   $$\partial_i\partial_j f(x)=\partial_j\partial_i f(x).$$
--   Here $\partial_j f(x)$ denotes the derivative of $f$ at $x$ along the $j$-th standard basis direction, and the outer derivative is taken of the function $x\mapsto\partial_jf(x)$.
--
--   This is the form of Clairaut's theorem that the rest of the mission uses: the derivation of the wave equation exchanges the order of two spatial derivatives at every application of the identity $\nabla\times(\nabla\times F)=\nabla(\nabla\cdot F)-\nabla^2F$.
-- source:
--   David Tong, Lectures on Electromagnetism, University of Cambridge Mathematical Tripos Part IB, Lent Term 2015, http://www.damtp.cam.ac.uk/user/tong/em.html — Section 4.3 "And There Was Light", pp. 82–86, equation (4.12) (the exchange of partial derivatives used in its derivation)

import Definitions.Def_TongEM_wave_ops

namespace TongEM

open Larmor

theorem pd_comm (f : Vec → ℝ) (hf : SmoothS f) (i j : Fin 3) (x : Vec) :
    pd i (pd j f) x = pd j (pd i f) x := by sorry

end TongEM
