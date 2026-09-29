-- Prove2me | Theorems.Thm_TongEM_dalembert_solution
-- name    : TongEM.dalembert_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T01:39:52.29275+00:00
-- url     : https://prove2.me/theorems/75682417-5830-400b-b1cb-f5834021a3b2
-- title:
--   $u(t,x)=f(x_0-ct)+g(x_0+ct)$ solves the wave equation
-- statement:
--   Let $c\neq0$ and let $f,g:\mathbb{R}\to\mathbb{R}$ be smooth ($C^\infty$) profiles. Then the scalar field
--   $$u(t,x)=f(x_0-ct)+g(x_0+ct),$$
--   depending on time and on the first spatial coordinate only, satisfies the wave equation
--   $$\frac{1}{c^2}\frac{\partial^2u}{\partial t^2}-\nabla^2u=0$$
--   at every time and every point: $f$ is a profile travelling to the right with speed $c$ and $g$ one travelling to the left.
--
--   This is the general one-dimensional solution quoted in Section 4.3.1 of Tong's lectures, immediately after equation (4.13). The statement is the "solutions exist" half of that discussion; the converse — that every solution depending only on $t$ and $x_0$ has this form — is not asserted here.
-- source:
--   David Tong, Lectures on Electromagnetism, University of Cambridge Mathematical Tripos Part IB, Lent Term 2015, http://www.damtp.cam.ac.uk/user/tong/em.html — Section 4.3 "And There Was Light", pp. 82–86, Section 4.3.1, the general solution $E(x,t)=f(x-ct)+g(x+ct)$ of equation (4.13)

import Definitions.Def_TongEM_wave_ops

namespace TongEM

open Larmor

theorem dalembert_solution (c : ℝ) (hc : c ≠ 0) (f g : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (t : ℝ) (x : Vec) :
    boxScalar c (fun s y => f (y 0 - c * s) + g (y 0 + c * s)) t x = 0 := by sorry

end TongEM
