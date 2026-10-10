-- Prove2me | Theorems.Thm_QuasiHemiVI_Existence_prop_2_5_ii
-- name    : QuasiHemiVI.Existence.prop_2_5_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:43.853811+00:00
-- url     : https://prove2.me/theorems/81854aea-a4a5-4bd0-8986-de89c317e2ca
-- title:
--   Proposition 2.5 (ii) — $J^0(x;v)=\max\{\langle\xi,v\rangle : \xi\in\partial J(x)\}$
-- statement:
--   Let $X$ be a real Banach space and $J:X\to\mathbb R$ locally Lipschitz. For every $x,v\in X$,
--
--   $$
--   J^0(x;v)=\max\{\langle\xi,v\rangle_{X^*\times X}\ :\ \xi\in\partial J(x)\},
--   $$
--
--   that is, $J^0(x;v)$ is an upper bound of $\{\langle\xi,v\rangle:\xi\in\partial J(x)\}$ and is attained by some $\xi\in\partial J(x)$.
--
--   This support-function formula converts the term $J^0(\gamma u;\gamma(v-u))$ of a hemivariational inequality into a pairing with an element of $\partial J(\gamma u)$; it is used in the proofs of Theorem 3.4 and Theorem 3.8.
--
--   **Formalization Note** "max" is stated as `IsGreatest` of the image set, which records both the upper bound and its attainment.
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1249, Proposition 2.5 (ii)

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv

namespace QuasiHemiVI.Existence

/-- Proposition 2.5 (ii), p. 1249: for a locally Lipschitz `J` on a Banach space `X`,
`J⁰(x; v) = max {⟨ξ, v⟩ | ξ ∈ ∂J(x)}` — the maximum is attained. -/
theorem prop_2_5_ii {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (J : X → ℝ) (hJ : LocallyLipschitz J) (x v : X) :
    IsGreatest ((fun ξ : X →L[ℝ] ℝ => ξ v) '' clarkeGrad J x) (clarkeDeriv J x v) := by sorry

end QuasiHemiVI.Existence
