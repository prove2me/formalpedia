-- Prove2me | Theorems.Thm_QuasiHemiVI_Existence_prop_2_5_i
-- name    : QuasiHemiVI.Existence.prop_2_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:11.042583+00:00
-- url     : https://prove2.me/theorems/3806f09b-92c8-4200-9b2e-83af43509b90
-- title:
--   Proposition 2.5 (i) — $v\mapsto J^0(x;v)$ is positively homogeneous and subadditive
-- statement:
--   Let $X$ be a real Banach space and $J:X\to\mathbb R$ locally Lipschitz, and let $x\in X$. Then the Clarke directional derivative $v\mapsto J^0(x;v)$ is positively homogeneous and subadditive:
--
--   $$
--   J^0(x;\lambda v)=\lambda J^0(x;v)\quad(\lambda\ge0,\ v\in X),\qquad J^0(x;v_1+v_2)\le J^0(x;v_1)+J^0(x;v_2)\quad(v_1,v_2\in X).
--   $$
--
--   These two properties make $J^0(x;\cdot)$ a sublinear function; the paper uses them to show that the sets $G(u)$ of the KKM-type argument are convex and to rescale test directions.
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1249, Proposition 2.5 (i)

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv

namespace QuasiHemiVI.Existence

/-- Proposition 2.5 (i), p. 1249: for a locally Lipschitz `J` on a Banach space `X` and every
`x`, the map `v ↦ J⁰(x; v)` is positively homogeneous (`J⁰(x; c v) = c J⁰(x; v)` for `c ≥ 0`) and subadditive. -/
theorem prop_2_5_i {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (J : X → ℝ) (hJ : LocallyLipschitz J) (x : X) :
    (∀ c : ℝ, 0 ≤ c → ∀ v : X, clarkeDeriv J x (c • v) = c * clarkeDeriv J x v) ∧
    (∀ v₁ v₂ : X, clarkeDeriv J x (v₁ + v₂) ≤ clarkeDeriv J x v₁ + clarkeDeriv J x v₂) := by sorry

end QuasiHemiVI.Existence
