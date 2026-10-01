-- Prove2me | Theorems.Thm_PolyhedralSOC_UpperBound_tower_composition
-- name    : PolyhedralSOC.UpperBound.tower_composition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:47:45.133648+00:00
-- url     : https://prove2.me/theorems/d6c03dc1-18cb-40a6-bc80-3501c22bf843
-- title:
--   §2, Eqs. (6)–(7) — composing planar approximations along the tower
-- statement:
--   Let $\theta\ge1$ and $k=2^\theta$. For $\ell=1,\dots,\theta$ let $\varepsilon_\ell>0$ and let $\Pi_\ell:\mathbb R^2\times\mathbb R\times\mathbb R^{p_\ell}\to\mathbb R^{q_\ell}$ be a polyhedral $\varepsilon_\ell$-approximation of $L^2=\{(x_1,x_2,x_3)\mid\sqrt{x_1^2+x_2^2}\le x_3\}$. Consider the linear system
--   $$\Pi_\ell\big(y_{2i-1}^{\ell-1},y_{2i}^{\ell-1},y_i^\ell,u_i^\ell\big)\ge0,\qquad i=1,\dots,2^{\theta-\ell},\ \ell=1,\dots,\theta,\tag{6}$$
--   in the tower variables $y_i^\ell$ (with $y_i^0=y_i$, $y_1^\theta=t$) and auxiliary vectors $u_i^\ell$. Then this system is a polyhedral $\varepsilon$-approximation of $L^k$ with
--   $$\varepsilon=\prod_{\ell=1}^{\theta}(1+\varepsilon_\ell)-1,\tag{7}$$
--   in the sense that
--   1. every $(y,t)\in L^k$ can be extended to tower variables and auxiliary vectors solving (6);
--   2. whenever $(y,t)$ extends to a solution of (6), $\|y\|_2\le\prod_{\ell=1}^\theta(1+\varepsilon_\ell)\,t$.
--
--   This reduces the approximation of $L^k$ to the approximation of the three-dimensional cone $L^2$.
--
--   **Formalization Note** The statement is made on solution sets of (6); the packaging of (6) into a single linear map $\Pi(y,t,u)$ (with the intermediate tower variables as part of $u$) is not formalized here. The norm is the Euclidean norm.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), §2, p. 199, Eqs. (6)–(7)

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
import Definitions.Def_PolyhedralSOC_UpperBound_Tower

namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), §2, Eqs. (6)–(7), p. 199 (PDF p. 7): if, for
`ℓ = 1, …, θ`, `Ps ℓ` is a polyhedral `ε_ℓ`-approximation of `L²`, then the system (6)
along the tower of `k = 2^θ` is a polyhedral `ε`-approximation of `L^k` with
`1 + ε = ∏_{ℓ=1}^θ (1 + ε_ℓ)` (Eq. (7)), stated on solution sets:
(i) every `(y, t) ∈ L^k` extends to tower variables and auxiliary vectors solving (6);
(ii) every solution of (6) satisfies `‖y‖₂ ≤ ∏_{ℓ=1}^θ (1 + ε_ℓ) · t`. -/
theorem tower_composition (θ : ℕ) (hθ : 1 ≤ θ) (p q : ℕ → ℕ) (ε : ℕ → ℝ)
    (Ps : (ℓ : ℕ) → (Fin 2 → ℝ) × ℝ × (Fin (p ℓ) → ℝ) →ₗ[ℝ] (Fin (q ℓ) → ℝ))
    (hε : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ θ → 0 < ε ℓ)
    (hP : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ θ → Shared.IsPolyhedralApprox 2 (p ℓ) (q ℓ) (ε ℓ) (Ps ℓ)) :
    (∀ (y : Fin (2 ^ θ) → ℝ) (t : ℝ), (y, t) ∈ Shared.LorentzCone (2 ^ θ) →
      ∃ (Y : ℕ → ℕ → ℝ) (U : (ℓ : ℕ) → ℕ → Fin (p ℓ) → ℝ),
        IsTowerOf θ y t Y ∧ TowerSystem6 θ p q Ps Y U) ∧
    (∀ (y : Fin (2 ^ θ) → ℝ) (t : ℝ) (Y : ℕ → ℕ → ℝ) (U : (ℓ : ℕ) → ℕ → Fin (p ℓ) → ℝ),
      IsTowerOf θ y t Y → TowerSystem6 θ p q Ps Y U →
        Shared.eucNorm y ≤ (∏ ℓ ∈ Finset.Icc 1 θ, (1 + ε ℓ)) * t) := by sorry

end PolyhedralSOC.UpperBound
