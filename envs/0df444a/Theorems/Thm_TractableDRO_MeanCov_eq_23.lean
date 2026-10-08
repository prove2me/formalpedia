-- Prove2me | Theorems.Thm_TractableDRO_MeanCov_eq_23
-- name    : TractableDRO.MeanCov.eq_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:46.975774+00:00
-- url     : https://prove2.me/theorems/50113d1a-cada-413a-85de-571c94c4249a
-- title:
--   Remark after Theorem 2, p. 910, (23) — π²(r⁰, r) as a conic optimization problem
-- statement:
--   Let $F \in \mathbb R^{N\times n}$, let $\Sigma \in \mathbb R^{N \times N}$ be symmetric positive semidefinite, let $\hat{\mathcal V} \subseteq \mathbb R^{n}$ be nonempty, and let $r^0 \in \mathbb R$, $r \in \mathbb R^{n}$. Then the bound $\pi^2$ of (22) equals the value of the problem
--
--   $$\pi^2(r^0, r) = \inf_{u \in \mathbb R,\ y \in \mathbb R^{N}} \Big\{ \tfrac12 u + \tfrac12 \sqrt{u^2 + y'\Sigma y} \ :\ r^0 + \sup_{\hat\zeta \in \hat{\mathcal V}} r'\hat\zeta \le u,\ \ F'y = r \Big\}.$$
--
--   Here $\sup_{\hat\zeta \in \hat{\mathcal V}} r'\hat\zeta$ may be $+\infty$, in which case no $u$ is feasible and both sides equal $+\infty$; an infeasible minimization has value $+\infty$.
--
--   This is (23) of Goh and Sim: when $\hat{\mathcal V}$ is conic representable, the constraint on $u$ is a robust linear constraint and the objective is second-order cone representable, so $\pi^2$ is computable by conic optimization.
--
--   **Formalization Note** The infimum and the supremum are taken in the extended reals (`EReal`); the paper's "inf" is not claimed to be attained. Nonemptiness of $\hat{\mathcal V}$ is required: for $\hat{\mathcal V} = \emptyset$ the left side is $-\infty$ (when $F'y = r$ is solvable) while the right side is an infimum of positive reals.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 910, Remark after Theorem 2, (23)

import Mathlib
import Definitions.Def_TractableDRO_MeanCov_Model

open Matrix

namespace TractableDRO.MeanCov

theorem eq_23 {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ) (Sig : Matrix (Fin N) (Fin N) ℝ)
    (Vhat : Set (Fin n → ℝ)) (hSig : Sig.PosSemidef) (hV : Vhat.Nonempty)
    (r0 : ℝ) (r : Fin n → ℝ) :
    pi2 F Sig Vhat r0 r =
      ⨅ (u : ℝ) (y : Fin N → ℝ)
        (_ : (r0 : EReal) + ⨆ ζh ∈ Vhat, ((r ⬝ᵥ ζh : ℝ) : EReal) ≤ (u : EReal))
        (_ : Fᵀ *ᵥ y = r),
        ((u / 2 + Real.sqrt (u ^ 2 + y ⬝ᵥ Sig *ᵥ y) / 2 : ℝ) : EReal) := by sorry

end TractableDRO.MeanCov
