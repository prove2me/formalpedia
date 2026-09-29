-- Prove2me | Theorems.Thm_SupplyChainFactoring_Extension_unconstrained_optimum_unimodal
-- name    : SupplyChainFactoring.Extension.unconstrained_optimum_unimodal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:29:12.806258+00:00
-- url     : https://prove2.me/theorems/05f5e8c1-d2b3-4ea5-8eb6-38d01397147a
-- title:
--   §5.3 — $\tau^*_0$ is the retailer's unconstrained optimal payment extension
-- statement:
--   In the Kouvelis–Xu model, fix ratings $C_s,C_r\in(C_{\min},C_{\max})$ and a wholesale price $w\le p$. Suppose $\tau^*_0\in\mathbb R$ and $q_0\in(0,\mathbb Z)$ solve the system
--   $$\lambda_r k(q_0)z(q_0)+\eta_r=2\eta_r e^{\lambda_r\tau^*_0},\qquad w\bar F(q_0)=c_{\mathcal R}(\tau^*_0).$$
--   Consider the retailer's reverse factoring profit $\Pi_{\mathcal R}(w,\tau)=e^{-\lambda_s t_1}(1-\rho_r)(2-e^{-\lambda_r\tau})(p-w)S(q_{\mathcal R})$, where $q_{\mathcal R}$ is the supplier's best response at $(w,\tau)$, on the set of extensions $\tau\in\mathbb R$ with $c_{\mathcal R}(\tau)<w$ (those at which the supplier produces). Then:
--   1. for $\tau_1\le\tau_2\le\tau^*_0$ in this set, $\Pi_{\mathcal R}(w,\tau_1)\le\Pi_{\mathcal R}(w,\tau_2)$;
--   2. for $\tau^*_0\le\tau_1\le\tau_2$ in this set, $\Pi_{\mathcal R}(w,\tau_2)\le\Pi_{\mathcal R}(w,\tau_1)$.
--
--   In particular $\tau^*_0$ maximizes the retailer's profit when neither the nonnegativity constraint nor the supplier's acceptance constraint is imposed, and the profit is unimodal around it. This is the property that makes the constrained optimum of problem (13) the projection of $\tau^*_0$ onto $[0,\tau_s]$.
--
--   **Formalization Note.** The paper says $\tau^*_0$ is "the optimal payment extension for the retailer's maximization problem in (16) without the nonnegativity constraint $\tau\ge0$". There is no problem (16); we read it as (13). Dropping only $\tau\ge0$ would keep the acceptance constraint $\tau\le\tau_s$ and make $\tau^*_0>\tau_s$ impossible, contrary to the projection formula of Proposition 6, so both constraints are dropped and the domain is the set where the supplier's best response is positive. "Optimal" is stated as unimodality, the form the projection formula uses. When $\lambda_r=0$ the first equation has no solution and the statement is vacuous, as in the paper.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6084, §5.3 (definition of τ*_0 after Proposition 6; problem (13))

import Mathlib
import Definitions.Def_SupplyChainFactoring_Extension_Model

namespace SupplyChainFactoring.Extension

/-- §5.3, p. 6084: `τ*_0`, solved from `{λ_r k(q)z(q) + η_r = 2η_r e^{λ_r τ}, w F̄(q) = c_𝓡(τ)}`,
is the optimal payment extension of the retailer's problem (13) without its constraints: on the
set of `τ ∈ ℝ` where the supplier's best response is positive (`c_𝓡(τ) < w`), the retailer's
profit `Π_𝓡` at the fixed wholesale price `w ≤ p` is nondecreasing up to `τ*_0` and
nonincreasing from `τ*_0` on. -/
theorem unconstrained_optimum_unimodal (M : Model) {Cs Cr w τ0 q0 : ℝ}
    (hCs : Cs ∈ Set.Ioo M.Cmin M.Cmax) (hCr : Cr ∈ Set.Ioo M.Cmin M.Cmax)
    (hwp : w ≤ M.p)
    (hq0 : M.InSupport q0)
    (hfoc : M.lamR * M.k q0 * M.z q0 + M.η Cr = 2 * M.η Cr * Real.exp (M.lamR * τ0))
    (hbr : w * M.Fbar q0 = M.cR Cs Cr τ0) :
    (∀ τ₁ τ₂ q₁ q₂ : ℝ, τ₁ ≤ τ₂ → τ₂ ≤ τ0 → M.cR Cs Cr τ₂ < w →
      M.IsBestResponse (M.ΛR Cr τ₁) Cs w q₁ → M.IsBestResponse (M.ΛR Cr τ₂) Cs w q₂ →
      M.retailerProfitR Cr τ₁ w q₁ ≤ M.retailerProfitR Cr τ₂ w q₂) ∧
    (∀ τ₁ τ₂ q₁ q₂ : ℝ, τ0 ≤ τ₁ → τ₁ ≤ τ₂ → M.cR Cs Cr τ₂ < w →
      M.IsBestResponse (M.ΛR Cr τ₁) Cs w q₁ → M.IsBestResponse (M.ΛR Cr τ₂) Cs w q₂ →
      M.retailerProfitR Cr τ₂ w q₂ ≤ M.retailerProfitR Cr τ₁ w q₁) := by sorry

end SupplyChainFactoring.Extension
