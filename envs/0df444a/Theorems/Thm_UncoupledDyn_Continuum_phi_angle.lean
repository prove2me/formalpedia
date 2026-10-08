-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_phi_angle
-- name    : UncoupledDyn.Continuum.phi_angle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:14.308933+00:00
-- url     : https://prove2.me/theorems/dab1f99a-2988-4241-a970-80b8009395b3
-- title:
--   Fn. 21, p. 1835 — φ rotates by an angle between 0 and π/4
-- statement:
--   Let $\varphi:D\to D$ be the explicit map of §II. For every $z\in D$ with $z\ne0$ there are $c>0$ and an angle $\theta\in[0,\pi/4]$ such that
--   $$\varphi(z)=c\,e^{i\theta}z,$$
--   i.e. $\varphi(z)$ is obtained from $z$ by a rotation by an angle between $0$ and $\pi/4$ followed by a positive scaling.
--
--   This is the angle property recalled in footnote 21 to prove the Appendix's conditions (3) and (4) on $\psi_a$.
--
--   **Formalization Note.** $\mathbb R^2$ is $\mathbb C$ and rotation by $\theta$ is multiplication by $e^{i\theta}$.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1835, fn. 21, clause "recalling that φ rotates by an angle between 0 and π/4"

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- Footnote 21, p. 1835: `φ` rotates by an angle between `0` and `π/4`: for every `z ∈ D`,
`z ≠ 0`, `φ(z)` is a positive multiple of `z` rotated by some `θ ∈ [0, π/4]`. -/
theorem phi_angle :
    ∀ z ∈ D, z ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      phi z = (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * z := by sorry

end UncoupledDyn.Continuum
