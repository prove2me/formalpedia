-- Prove2me | Theorems.Thm_SupplyChainFactoring_Extension_factoring_choice
-- name    : SupplyChainFactoring.Extension.factoring_choice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:28:22.309701+00:00
-- url     : https://prove2.me/theorems/966dfa68-fc6d-476c-b064-9293c4336134
-- title:
--   Proposition 4 — the supplier's choice between recourse and non-recourse factoring
-- statement:
--   In the Kouvelis–Xu model, fix the retailer's rating $C_r\in(C_{\min},C_{\max})$. Let $\mathbb C_{\mathcal N}$, $\mathbb C_{\mathcal F}$ and $\mathbb C_1$ be the unique values of $C_s$ in $(C_{\min},C_{\max})$ that satisfy, respectively, $c_{\mathcal N}=p$, $c_{\mathcal F}=p$, and
--   $$(1-\rho_r)+(1-\rho_s)-e^{\eta_s t_2}=e^{-\eta_r t_2}(1-\rho_r).$$
--   When both factoring schemes are available to the supplier, for every $C_s\in(C_{\min},C_{\max})$:
--   1. non-recourse factoring is adopted if and only if $\mathbb C_{\mathcal N}<C_s\le\mathbb C_1$;
--   2. recourse factoring is adopted if and only if $C_s>\mathbb C_{\mathcal F}\vee\mathbb C_1=\max\{\mathbb C_{\mathcal F},\mathbb C_1\}$.
--
--   Here "adopted" compares the supplier's equilibrium profits of the feasible schemes, with ties going to non-recourse factoring. The result identifies the existing equilibrium in force before the retailer offers reverse factoring, which is the benchmark of the payment extension problem (13).
--
--   **Formalization Note.** The paper writes "should be adopted" without a formal definition. We read it as: the scheme is feasible (some wholesale price $w\ge0$ with a supplier best response gives the retailer positive profit) and its equilibrium supplier profit is at least (non-recourse) or strictly above (recourse) that of every equilibrium of the other scheme whenever the other is feasible. The tie order is forced by $C_s=\mathbb C_1$ belonging to case 1. Each threshold is a hypothesis "the unique point of $(C_{\min},C_{\max})$ satisfying the equation", with $c_{\mathcal N}=p$ and $c_{\mathcal F}=p$ cross-multiplied.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6080, Proposition 4

import Mathlib
import Definitions.Def_SupplyChainFactoring_Extension_Model

namespace SupplyChainFactoring.Extension

/-- Proposition 4, p. 6080: with both factoring schemes available, non-recourse factoring is
adopted iff `ℂ_𝓝 < Cs ≤ ℂ_1`, and recourse factoring is adopted iff `Cs > ℂ_𝓕 ∨ ℂ_1`. -/
theorem factoring_choice (M : Model) {Cr CN CF C1 : ℝ}
    (hCr : Cr ∈ Set.Ioo M.Cmin M.Cmax)
    (hCN : M.IsThresholdN Cr CN) (hCF : M.IsThresholdF Cr CF) (hC1 : M.IsThreshold1 Cr C1) :
    ∀ Cs ∈ Set.Ioo M.Cmin M.Cmax,
      (M.AdoptedNonRecourse Cs Cr ↔ CN < Cs ∧ Cs ≤ C1) ∧
      (M.AdoptedRecourse Cs Cr ↔ max CF C1 < Cs) := by sorry

end SupplyChainFactoring.Extension
