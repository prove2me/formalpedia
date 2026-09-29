-- Prove2me | Theorems.Thm_SupplyChainFactoring_Extension_maximal_acceptable_extension
-- name    : SupplyChainFactoring.Extension.maximal_acceptable_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:28:44.168214+00:00
-- url     : https://prove2.me/theorems/da6eb6f3-5d1e-4b6a-a96d-ed6ff907b9f5
-- title:
--   §5.3 — $\tau_s$ is the maximal payment extension the supplier accepts
-- statement:
--   In the Kouvelis–Xu model, fix ratings $C_s,C_r\in(C_{\min},C_{\max})$ and the thresholds $\mathbb C_{\mathcal N}$, $\mathbb C_{\mathcal F}$, $\mathbb C^{\max}_{\mathcal R}$ (unique solutions in $C_s$ of $c_{\mathcal N}=p$, $c_{\mathcal F}=p$ and $(1-\rho_r)+(1-\rho_s)-e^{\eta_s t_2}=e^{-\eta_r t_2}$). The retailer offers reverse factoring at the existing wholesale price $w_s$; the supplier accepts an extension $\tau$ when his best-response profit under reverse factoring at $(w_s,\tau)$ is at least his existing equilibrium profit $\pi_s$.
--
--   1. **Non-recourse benchmark.** If $\mathbb C_{\mathcal N}<C_s$ and $(w_s,q_s)$ is a non-recourse equilibrium, let
--   $$\tau_s=-\eta_r^{-1}\ln(1-\rho_r).$$
--   Then $\tau_s\ge0$, and for every $\tau\ge0$ the constraints of problem (13) can be met at $\tau$ if and only if $\tau\le\tau_s$.
--   2. **Recourse benchmark.** If $\mathbb C_{\mathcal F}<C_s<\mathbb C^{\max}_{\mathcal R}$ and $(w_s,q_s)$ is a recourse equilibrium, let
--   $$\tau_s=-\eta_r^{-1}\ln\bigl[(1-\rho_r)+(1-\rho_s)-e^{\eta_s t_2}\bigr]-t_2.$$
--   Then $\tau_s>0$, and for every $\tau\ge0$ the constraints of problem (13) can be met at $\tau$ if and only if $\tau\le\tau_s$.
--
--   The acceptance constraint of (13) is thereby reduced to the box $0\le\tau\le\tau_s$, which is why the optimal extension of Proposition 6 is a projection onto $[0,\tau_s]$.
--
--   **Formalization Note.** The paper's acceptance constraint is $\pi^*_{\mathcal R}\ge\max\{\pi^*_{\mathcal F},\pi^*_{\mathcal N}\}$. We read $\pi^*_{\mathcal R}$ as the supplier's best-response profit under reverse factoring at $(w_s,\tau)$, and $\max\{\pi^*_{\mathcal F},\pi^*_{\mathcal N}\}$ as the supplier's profit in the existing equilibrium, i.e. the adopted scheme of Proposition 4. The hypotheses keep only what each case needs: the case conditions $C_s\le\mathbb C_1$ and $C_s>\mathbb C_1$ of the paper's display are not required.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6084, §5.3 (definition of τ_s after Proposition 6)

import Mathlib
import Definitions.Def_SupplyChainFactoring_Extension_Model

namespace SupplyChainFactoring.Extension

/-- §5.3, p. 6084: `τ_s` is the maximal payment extension that the supplier accepts.
Non-recourse case (existing equilibrium `(w*_𝓝, q*_𝓝)`, `τ_s = −η_r⁻¹ ln(1 − ρ_r)`) and
recourse case (existing equilibrium `(w*_𝓕, q*_𝓕)`,
`τ_s = −η_r⁻¹ ln[(1 − ρ_r) + (1 − ρ_s) − e^{η_s t_2}] − t_2`): for `τ ≥ 0`, the constraints of
problem (13) can be met at `τ` iff `τ ≤ τ_s`. -/
theorem maximal_acceptable_extension (M : Model) {Cs Cr CN CF CRmax : ℝ}
    (hCs : Cs ∈ Set.Ioo M.Cmin M.Cmax) (hCr : Cr ∈ Set.Ioo M.Cmin M.Cmax)
    (hCN : M.IsThresholdN Cr CN) (hCF : M.IsThresholdF Cr CF)
    (hCRmax : M.IsThresholdRmax Cr CRmax) :
    (CN < Cs → ∀ ws qs : ℝ, M.IsEquilibrium (M.ΛN Cr) Cs Cr ws qs →
      0 ≤ -Real.log (1 - M.ρ Cr) / M.η Cr ∧
      ∀ τ : ℝ, 0 ≤ τ →
        ((∃ q : ℝ, M.FeasibleExtension Cs Cr ws (M.supplierProfit (M.ΛN Cr) Cs ws qs) τ q) ↔
          τ ≤ -Real.log (1 - M.ρ Cr) / M.η Cr)) ∧
    (CF < Cs → Cs < CRmax → ∀ ws qs : ℝ, M.IsEquilibrium (M.ΛF Cs Cr) Cs Cr ws qs →
      0 < -Real.log (M.ΛF Cs Cr) / M.η Cr - M.t2 ∧
      ∀ τ : ℝ, 0 ≤ τ →
        ((∃ q : ℝ, M.FeasibleExtension Cs Cr ws (M.supplierProfit (M.ΛF Cs Cr) Cs ws qs) τ q) ↔
          τ ≤ -Real.log (M.ΛF Cs Cr) / M.η Cr - M.t2)) := by sorry

end SupplyChainFactoring.Extension
