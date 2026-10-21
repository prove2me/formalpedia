-- Prove2me | Theorems.Thm_SystemicHoldings_FEfficient_msd_value
-- name    : SystemicHoldings.FEfficient.msd_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:21.412832+00:00
-- url     : https://prove2.me/theorems/1d97c932-a94d-4aff-9998-04fef3f4dc0c
-- title:
--   Proof of Theorem 4.1 a), EC p. 10 — MSD(Q*) = (y*)ᵀGy* = (bᵀv)²/(1ᵀz) = (bᵀv)²/(1ᵀG⁻¹1)
-- statement:
--   Let $K\ge1$, $\mu,\sigma\in\mathbb R^K$ with all $\sigma_k>0$, and $b,v\in\mathbb R^N$. With $z=G^{-1}\mathbf 1_K$ and $y^*=\frac{b^\top v}{\mathbf 1_K^\top z}z$,
--   $$(y^*)^\top G y^* = \frac{(b^\top v)^2}{\mathbf 1_K^\top z},$$
--   and every holding matrix $Q$ with $Qv=y^*$ has
--   $$\mathrm{MSD}(Q) = (Qv)^\top G(Qv) = \frac{(b^\top v)^2}{\mathbf 1_K^\top G^{-1}\mathbf 1_K}.$$
--
--   This is the computation of the minimal mean squared deviation in part a) of Theorem 4.1.
--
--   **Formalization Note** $K\ge1$ is added so that $\mathbf 1_K^\top z\neq0$.
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, E-Companion p. 10 (PDF 40), proof of Theorem 4.1 a)

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

namespace SystemicHoldings.FEfficient
open Matrix

theorem msd_value {K N : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (b v : Fin N → ℝ) :
    yStar μ σ b v ⬝ᵥ (shockMoment μ σ *ᵥ yStar μ σ b v) =
      (b ⬝ᵥ v) ^ 2 / ((fun _ => (1 : ℝ)) ⬝ᵥ zVec μ σ) ∧
    ∀ Q : Matrix (Fin K) (Fin N) ℝ, Q *ᵥ v = yStar μ σ b v →
      msd μ σ v Q = (b ⬝ᵥ v) ^ 2 /
        ((fun _ => (1 : ℝ)) ⬝ᵥ ((shockMoment μ σ)⁻¹ *ᵥ (fun _ => (1 : ℝ)))) := by sorry

end SystemicHoldings.FEfficient
