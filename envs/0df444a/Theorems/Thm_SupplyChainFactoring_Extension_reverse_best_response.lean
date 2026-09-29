-- Prove2me | Theorems.Thm_SupplyChainFactoring_Extension_reverse_best_response
-- name    : SupplyChainFactoring.Extension.reverse_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:27:51.001888+00:00
-- url     : https://prove2.me/theorems/8c220e71-4ade-44e7-953d-9b4d53e8cbf7
-- title:
--   Eq. (12) — the supplier's best response under reverse factoring
-- statement:
--   In the Kouvelis–Xu model, fix a supplier rating $C_s\in(C_{\min},C_{\max})$, a retailer rating $C_r$, a wholesale price $w$ and a payment extension $\tau$. Let $c_{\mathcal R}(\tau)=c\,e^{(\eta_s+\lambda_s)t_1+\eta_r(t_2+\tau)}$ be the effective unit production cost in reverse factoring, and consider the supplier's profit $\pi_{\mathcal R}(q;w,\tau)=(1-\rho_s)\bigl(e^{-\eta_r(t_2+\tau)}e^{-\lambda_s t_1}wS(q)-c\,q\,e^{\eta_s t_1}\bigr)$ over $q\ge0$.
--
--   1. If $c_{\mathcal R}(\tau)<w$, then $q$ is a best response if and only if $0<q<\mathbb Z$ and
--   $$w\bar F(q)=c_{\mathcal R}(\tau).$$
--   2. If $w\le c_{\mathcal R}(\tau)$, then the only best response is $q=0$.
--
--   This is the follower's side of the reverse factoring game: the production quantity is the unique solution of Eq. (12), and the retailer's problem (13) is written in terms of it.
--
--   **Formalization Note.** The paper states only the first-order condition (12). The case $w\le c_{\mathcal R}(\tau)$, where no positive quantity is profitable, is the boundary case the paper leaves implicit. The statement is made for every real $\tau$ (the paper has $\tau\ge0$) because the analysis of $\tau^*_0$ uses negative extensions too.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6082, Eq. (12)

import Mathlib
import Definitions.Def_SupplyChainFactoring_Extension_Model

namespace SupplyChainFactoring.Extension

/-- Eq. (12), p. 6082: the supplier's best response under reverse factoring at `(w, τ)`.
If `c_𝓡(τ) < w`, the best responses are exactly the `q ∈ (0, Z)` with `w F̄(q) = c_𝓡(τ)`;
if `w ≤ c_𝓡(τ)`, the only best response is `q = 0`. -/
theorem reverse_best_response (M : Model) {Cs Cr w τ : ℝ}
    (hCs : Cs ∈ Set.Ioo M.Cmin M.Cmax) :
    (M.cR Cs Cr τ < w → ∀ q : ℝ,
      M.IsBestResponse (M.ΛR Cr τ) Cs w q ↔ (M.InSupport q ∧ w * M.Fbar q = M.cR Cs Cr τ)) ∧
    (w ≤ M.cR Cs Cr τ → ∀ q : ℝ, M.IsBestResponse (M.ΛR Cr τ) Cs w q ↔ q = 0) := by sorry

end SupplyChainFactoring.Extension
