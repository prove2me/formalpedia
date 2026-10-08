-- Prove2me | Theorems.Thm_WheelerDeWittSuperspace_velocityQuad_cone
-- name    : WheelerDeWittSuperspace.velocityQuad_cone
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T22:05:55.559983+00:00
-- url     : https://prove2.me/theorems/d40084da-7d0f-4c78-ace4-2d0ad8b6d77c
-- title:
--   DeWitt's intrinsic time: superspace fibre is a Lorentzian cone
-- statement:
--   Write $h=s\hat h$ with $s>0$, $\hat h$ positive definite and $\det\hat h=1$, and a velocity $k=ds\,\hat h+s\,d\hat h$ with $\operatorname{tr}(\hat h^{-1}d\hat h)=0$. Then
--   $$\sqrt{\det h}\,\big(\operatorname{tr}(h^{-1}kh^{-1}k)-(\operatorname{tr}h^{-1}k)^2\big)=-d\tau^2+\tfrac{3}{32}\,\tau^2\,\operatorname{tr}\big((\hat h^{-1}d\hat h)^2\big),$$
--   where $\tau=\sqrt{32/3}\,s^{3/4}$ and $d\tau=\tfrac34\sqrt{32/3}\,s^{-1/4}\,ds$. The local volume $\tau\propto(\det h)^{1/4}$ is a timelike coordinate and the cone has no cross term.
-- source:
--   B. S. DeWitt, Quantum Theory of Gravity I. The Canonical Theory, Phys. Rev. 160 (1967) 1113-1148, https://doi.org/10.1103/PhysRev.160.1113, Section 5 (fibre metric and intrinsic time)

import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- Milestone 3 (DeWitt's intrinsic time): split `h = s ĥ` with `det ĥ = 1`. On
velocities `k = ds ĥ + s dĥ` with `tr(ĥ⁻¹ dĥ) = 0`, the supermetric is the Lorentzian
cone `-dτ² + (3/32) τ² tr((ĥ⁻¹dĥ)²)`, where `τ = √(32/3) s^{3/4}`. -/
theorem velocityQuad_cone (mh dh : Matrix (Fin 3) (Fin 3) ℝ) (hmh : mh.PosDef)
    (hdet : mh.det = 1) (htr : (mh⁻¹ * dh).trace = 0) (s ds : ℝ) (hs : 0 < s) :
    velocityQuad (s • mh) (ds • mh + s • dh) =
      -((3 / 4) * Real.sqrt (32 / 3) * s ^ (-(1 / 4 : ℝ)) * ds) ^ 2 +
        (3 / 32) * (Real.sqrt (32 / 3) * s ^ (3 / 4 : ℝ)) ^ 2 *
          ((mh⁻¹ * dh) * (mh⁻¹ * dh)).trace := by sorry

end WheelerDeWittSuperspace
