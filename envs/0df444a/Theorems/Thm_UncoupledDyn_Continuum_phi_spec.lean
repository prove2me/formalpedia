-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_phi_spec
-- name    : UncoupledDyn.Continuum.phi_spec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:59.932199+00:00
-- url     : https://prove2.me/theorems/f29d845d-4837-44cc-9ca8-5eff310d9038
-- title:
--   §II, p. 1831 — the explicit φ : D → D is continuous, equals 2z near 0, and φ(φ(z)) ≠ z for z ≠ 0
-- statement:
--   Let $D\subset\mathbb R^2$ be the closed unit disk and let $\varphi$ be the explicit map of §II: $\varphi(z)=2z$ for $\|z\|\le\frac13$, $\varphi$ is the rotation by $\pi/4$ on $\|z\|=1$, and $\varphi$ is affine in the radius on each ray between $\|z\|=\frac13$ and $\|z\|=1$. Then:
--   1. $\varphi$ is continuous on $D$ and maps $D$ into $D$;
--   2. $\varphi(z)=2z$ for every $z$ with $\|z\|\le\frac13$, in particular on a neighborhood of $0$;
--   3. for every $z\in D$ with $z\ne0$,
--   $$\varphi(\varphi(z))\ne z.$$
--
--   These are the two properties the paper asks of $\varphi$, and they make $0$ the only solution of $\varphi(\varphi(z))=z$, so that the game $\Gamma_0$ built from $\varphi$ has a unique Nash equilibrium.
--
--   **Formalization Note.** $\mathbb R^2$ is $\mathbb C$. The neighborhood of $0$ on which $\varphi(z)=2z$ is the disk $\|z\|\le\frac13$ of the page's own example.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1831, §II, the two bullets on φ and the sentence "Such a function clearly exists; for instance, …"

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- §II, p. 1831: the explicit `φ` is a continuous map `D → D` with `φ(z) = 2z` for `‖z‖ ≤ 1/3`
(a neighborhood of `0`) and `φ(φ(z)) ≠ z` for every `z ∈ D`, `z ≠ 0`. -/
theorem phi_spec :
    ContinuousOn phi D ∧ Set.MapsTo phi D D ∧ (∀ z : ℂ, ‖z‖ ≤ 1 / 3 → phi z = 2 * z) ∧
      ∀ z ∈ D, z ≠ 0 → phi (phi z) ≠ z := by sorry

end UncoupledDyn.Continuum
