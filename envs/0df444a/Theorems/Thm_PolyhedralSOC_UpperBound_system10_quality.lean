-- Prove2me | Theorems.Thm_PolyhedralSOC_UpperBound_system10_quality
-- name    : PolyhedralSOC.UpperBound.system10_quality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:49:41.591399+00:00
-- url     : https://prove2.me/theorems/48ab68f6-d17e-46bb-9c2d-3a83a14f2717
-- title:
--   Proof of Theorem 1.1 — system (10) approximates $L^{2^\theta}$ with quality $\beta(\nu_1,\dots,\nu_\theta)$
-- statement:
--   Let $\theta\ge1$, $k=2^\theta$, and let $\nu_1,\dots,\nu_\theta$ be positive integers. Then system (10) (system (8) with parameter $\nu_\ell$ placed on every triple $(y_{2i-1}^{\ell-1},y_{2i}^{\ell-1},y_i^\ell)$ of the tower of variables) describes a polyhedral approximation of $L^k$ of quality
--   $$\beta(\nu_1,\dots,\nu_\theta)=\prod_{\ell=1}^{\theta}\frac{1}{\cos\big(\frac{\pi}{2^{\nu_\ell+1}}\big)}-1,$$
--   that is:
--   1. every $(y,t)\in L^k$ can be extended (by tower variables $y_i^\ell$ with $y_i^0=y_i$, $y_1^\theta=t$, and variables $\xi_{\ell,i}^j,\eta_{\ell,i}^j$) to a solution of (10);
--   2. whenever $(y,t)$ extends to a solution of (10),
--   $$\|y\|_2\le\prod_{\ell=1}^{\theta}\frac{1}{\cos\big(\frac{\pi}{2^{\nu_\ell+1}}\big)}\;t=(1+\beta)\,t.$$
--
--   This is property 3 of the approximation in the proof of Theorem 1.1.
--
--   **Formalization Note** Stated on solution sets; the size counts (properties 1–2 of the paper) concern the encoding of (10) as a linear map and are not part of this statement. The norm is the Euclidean norm.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), proof of Theorem 1.1, pp. 200–201, system (10) and property 3

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone
import Definitions.Def_PolyhedralSOC_UpperBound_Tower
import Definitions.Def_PolyhedralSOC_UpperBound_System10

namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), proof of Theorem 1.1, system (10) and its
property 3, pp. 200–201 (PDF pp. 8–9): for `k = 2^θ`, `θ ≥ 1`, and positive integers
`ν_1, …, ν_θ`, the system (10) describes a polyhedral approximation of `L^k` of quality
`β = ∏_{ℓ=1}^θ 1/cos(π/2^{ν_ℓ+1}) − 1`, stated on solution sets:
(i) every `(y, t) ∈ L^k` extends to a solution of (10);
(ii) every solution of (10) satisfies `‖y‖₂ ≤ (1 + β) t`. -/
theorem system10_quality (θ : ℕ) (hθ : 1 ≤ θ) (νs : ℕ → ℕ)
    (hν : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ θ → 1 ≤ νs ℓ) :
    (∀ (y : Fin (2 ^ θ) → ℝ) (t : ℝ), (y, t) ∈ Shared.LorentzCone (2 ^ θ) →
      ∃ (Y : ℕ → ℕ → ℝ) (ξ η : ℕ → ℕ → ℕ → ℝ),
        IsTowerOf θ y t Y ∧ System10 θ νs Y ξ η) ∧
    (∀ (y : Fin (2 ^ θ) → ℝ) (t : ℝ) (Y : ℕ → ℕ → ℝ) (ξ η : ℕ → ℕ → ℕ → ℝ),
      IsTowerOf θ y t Y → System10 θ νs Y ξ η →
        Shared.eucNorm y ≤ (∏ ℓ ∈ Finset.Icc 1 θ, 1 / Real.cos (Real.pi / 2 ^ (νs ℓ + 1))) * t) := by sorry

end PolyhedralSOC.UpperBound
