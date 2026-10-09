-- Prove2me | Theorems.Thm_SupplyChainFactoring_Extension_optimal_payment_extension
-- name    : SupplyChainFactoring.Extension.optimal_payment_extension
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:29:46.307619+00:00
-- url     : https://prove2.me/theorems/874ca1bf-95bf-4f0d-a1bc-a6435b326b12
-- title:
--   Proposition 6 — the retailer's optimal reverse factoring payment extension
-- statement:
--   In the Kouvelis–Xu model, fix ratings $C_s,C_r\in(C_{\min},C_{\max})$. Let $\mathbb C_{\mathcal N}$, $\mathbb C_{\mathcal F}$, $\mathbb C_1$ be the thresholds of Propositions 2–4, and let $\mathbb C^{\max}_{\mathcal R}$ be the unique value of $C_s$ that satisfies $(1-\rho_r)+(1-\rho_s)-e^{\eta_s t_2}=e^{-\eta_r t_2}$.
--
--   **(i)** If $C_s\ge\mathbb C^{\max}_{\mathcal R}$, reverse factoring is dominated by recourse factoring: for every $\tau\ge0$ and every wholesale price $w$, the supplier's best-response profit under reverse factoring at $(w,\tau)$ is at most his best-response profit under recourse factoring at $w$.
--
--   **(ii)** If $\mathbb C_{\mathcal N}<C_s<\mathbb C^{\max}_{\mathcal R}$, let $\tau^*_0$ be solved, together with some $q\in(0,\mathbb Z)$, from
--   $$\lambda_r k(q)z(q)+\eta_r=2\eta_r e^{\lambda_r\tau},\qquad w_s\bar F(q)=c_{\mathcal R}(\tau),$$
--   where
--   $$(w_s,\tau_s)=\begin{cases}\bigl(w^*_{\mathcal N},\,-\eta_r^{-1}\ln(1-\rho_r)\bigr), & \mathbb C_{\mathcal N}<C_s\le\mathbb C_1,\\ \bigl(w^*_{\mathcal F},\,-\eta_r^{-1}\ln[(1-\rho_r)+(1-\rho_s)-e^{\eta_s t_2}]-t_2\bigr), & \mathbb C_{\mathcal F}\vee\mathbb C_1<C_s<\mathbb C^{\max}_{\mathcal R},\end{cases}$$
--   with $(w^*_{\mathcal N},q^*_{\mathcal N})$, resp. $(w^*_{\mathcal F},q^*_{\mathcal F})$, the existing equilibrium. Then reverse factoring should be offered with the payment extension
--   $$\tau^*_{\mathcal R}=\Xi_{[0,\tau_s]}(\tau^*_0)=\max\{0,\min\{\tau_s,\tau^*_0\}\}:$$
--   in each case there is a supplier best response $q$ at $(w_s,\tau^*_{\mathcal R})$ such that $(\tau^*_{\mathcal R},q)$ solves the retailer's problem (13) at the fixed wholesale price $w_s$, and the retailer's profit $\Pi_{\mathcal R}(w_s,\tau^*_{\mathcal R})$ is at least her existing equilibrium profit.
--
--   This is the paper's answer to the question of §5.3: which suppliers should be offered reverse factoring, and with what payment extension, when the wholesale price stays at its existing equilibrium value.
--
--   **Formalization Note.** "Dominated" in (i) is read at the supplier's level: he never strictly prefers any reverse factoring offer to recourse factoring at the same wholesale price. "Should be offered" in (ii) is read as: $\tau^*_{\mathcal R}$ is optimal in (13) and the retailer gains weakly relative to the existing equilibrium. In (13) the wholesale price is fixed at $w_s$ (§5.3, first sentence, and footnote 23). The acceptance constraint compares the supplier's best-response profit under reverse factoring with his existing equilibrium profit. The existing equilibrium enters as a hypothesis "$(w_s,q_s)$ is an equilibrium of the non-recourse (resp. recourse) game", and $\tau^*_0$ as a hypothesis that it and some $q$ solve the two equations; the paper does not argue that such a solution exists. The misprint $\Xi_{[0,z]}(x)=0$ "if $x<z$" is corrected to "if $x<0$". The paper's "problem in (16)" refers to (13).
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6084, Proposition 6

import Mathlib
import Definitions.Def_SupplyChainFactoring_Extension_Model

namespace SupplyChainFactoring.Extension

/-- Proposition 6, p. 6084: the retailer's optimal reverse factoring strategy.
(i) If `Cs ≥ ℂ^max_𝓡`, reverse factoring is dominated by recourse factoring: for every
`τ ≥ 0` and every wholesale price `w`, the supplier's best-response profit under reverse
factoring is at most his best-response profit under recourse factoring.
(ii) If `ℂ_𝓝 < Cs < ℂ^max_𝓡`, then in each case of the display, with `(w_s, q_s)` the existing
equilibrium, `τ_s` as displayed and `τ*_0` solved from the two equations, the extension
`τ*_𝓡 = Ξ_{[0,τ_s]}(τ*_0)` solves problem (13), and the retailer's profit there is at least her
existing equilibrium profit. -/
theorem optimal_payment_extension (M : Model) {Cs Cr CN CF C1 CRmax : ℝ}
    (hCs : Cs ∈ Set.Ioo M.Cmin M.Cmax) (hCr : Cr ∈ Set.Ioo M.Cmin M.Cmax)
    (hCN : M.IsThresholdN Cr CN) (hCF : M.IsThresholdF Cr CF) (hC1 : M.IsThreshold1 Cr C1)
    (hCRmax : M.IsThresholdRmax Cr CRmax) :
    -- (i)
    (CRmax ≤ Cs → ∀ τ w qR qF : ℝ, 0 ≤ τ →
      M.IsBestResponse (M.ΛR Cr τ) Cs w qR → M.IsBestResponse (M.ΛF Cs Cr) Cs w qF →
      M.supplierProfit (M.ΛR Cr τ) Cs w qR ≤ M.supplierProfit (M.ΛF Cs Cr) Cs w qF) ∧
    -- (ii)
    (CN < Cs → Cs < CRmax →
      -- first case: ℂ_𝓝 < Cs ≤ ℂ_1, existing non-recourse equilibrium
      (Cs ≤ C1 → ∀ ws qs τ0 q0 : ℝ, M.IsEquilibrium (M.ΛN Cr) Cs Cr ws qs →
        M.InSupport q0 →
        M.lamR * M.k q0 * M.z q0 + M.η Cr = 2 * M.η Cr * Real.exp (M.lamR * τ0) →
        ws * M.Fbar q0 = M.cR Cs Cr τ0 →
        ∃ q : ℝ,
          M.IsOptimalExtension Cs Cr ws (M.supplierProfit (M.ΛN Cr) Cs ws qs)
            (Xi (-Real.log (1 - M.ρ Cr) / M.η Cr) τ0) q ∧
          M.retailerProfit Cr ws qs ≤
            M.retailerProfitR Cr (Xi (-Real.log (1 - M.ρ Cr) / M.η Cr) τ0) ws q) ∧
      -- second case: ℂ_𝓕 ∨ ℂ_1 < Cs < ℂ^max_𝓡, existing recourse equilibrium
      (max CF C1 < Cs → ∀ ws qs τ0 q0 : ℝ, M.IsEquilibrium (M.ΛF Cs Cr) Cs Cr ws qs →
        M.InSupport q0 →
        M.lamR * M.k q0 * M.z q0 + M.η Cr = 2 * M.η Cr * Real.exp (M.lamR * τ0) →
        ws * M.Fbar q0 = M.cR Cs Cr τ0 →
        ∃ q : ℝ,
          M.IsOptimalExtension Cs Cr ws (M.supplierProfit (M.ΛF Cs Cr) Cs ws qs)
            (Xi (-Real.log (M.ΛF Cs Cr) / M.η Cr - M.t2) τ0) q ∧
          M.retailerProfit Cr ws qs ≤
            M.retailerProfitR Cr (Xi (-Real.log (M.ΛF Cs Cr) / M.η Cr - M.t2) τ0) ws q)) := by sorry

end SupplyChainFactoring.Extension
