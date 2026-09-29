-- Prove2me | Theorems.Thm_SupplyChainFactoring_Choice_supplier_preference_coef
-- name    : SupplyChainFactoring.Choice.supplier_preference_coef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:25:42.252068+00:00
-- url     : https://prove2.me/theorems/2f275d77-4cc3-4186-a54d-bcdb297befcf
-- title:
--   §4.4 (Lemma EC.2) — the supplier's preference between feasible schemes is a comparison of the $\Lambda_i$
-- statement:
--   Fix the model data and demand of the definitions, a retailer rating $C_r \in (C_{\min}, C_{\max})$, a payment extension $\tau \ge 0$ and a supplier rating $C_s \in (C_{\min}, C_{\max})$. Let $i, j$ be two feasible schemes among $\mathcal F, \mathcal N, \mathcal R$, and let $(w^*_i, q^*_i)$, $(w^*_j, q^*_j)$ be equilibria of the respective games, with supplier profits $\pi^*_i = \pi_i(q^*_i; w^*_i)$ and $\pi^*_j = \pi_j(q^*_j; w^*_j)$. Then
--
--   $$\pi^*_i \le \pi^*_j \iff \Lambda_i \le \Lambda_j, \qquad \pi^*_i < \pi^*_j \iff \Lambda_i < \Lambda_j.$$
--
--   The supplier therefore ranks feasible schemes by their coefficients $\Lambda_i$ alone. This is what turns the comparison of equilibrium profits in Propositions 4 and 5 into a comparison of explicit functions of the credit ratings.
--
--   **Formalization Note** The paper states this for "the two different factoring schemes" $\mathcal F$, $\mathcal N$; on p. 6082 it writes the reverse-factoring profit "using Equation (10)" with $\Lambda_{\mathcal R}$, so the statement is made for any pair among $\mathcal F, \mathcal N, \mathcal R$ (the same claim for the common form (10)). The result is Lemma EC.2 of Online Appendix B, reported in the main text.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6080, §4.4 (Lemma EC.2 of Online Appendix B); p. 6082 (π_𝓡 in the form of Eq. (10))

import Mathlib
import Definitions.Def_SupplyChainFactoring_Choice_Demand
import Definitions.Def_SupplyChainFactoring_Choice_Model

open MeasureTheory Real

namespace SupplyChainFactoring.Choice

/-- Kouvelis–Xu 2021, §4.4 (p. 6080; Lemma EC.2 of the Online Appendix): the supplier's preference
between two feasible schemes is a comparison of their coefficients `Λ_i`. For any two feasible
schemes `i, j` and any equilibria of them, the supplier's equilibrium profit under `i` is at most
(strictly below) that under `j` iff `Λ_i ≤ Λ_j` (`Λ_i < Λ_j`). -/
theorem supplier_preference_coef (P : Params) (hP : P.Valid) (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal)
    (hD : DemandModel μ f Z) (Cr : ℝ) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∀ Cs ∈ Set.Ioo P.Cmin P.Cmax, ∀ i j : Scheme,
      Feasible P μ i Cs Cr τ → Feasible P μ j Cs Cr τ →
      ∀ wi qi wj qj : ℝ, IsEquilibrium P μ i Cs Cr τ wi qi → IsEquilibrium P μ j Cs Cr τ wj qj →
        (supplierProfit P μ i Cs Cr τ wi qi ≤ supplierProfit P μ j Cs Cr τ wj qj ↔
            coef P i Cs Cr τ ≤ coef P j Cs Cr τ) ∧
        (supplierProfit P μ i Cs Cr τ wi qi < supplierProfit P μ j Cs Cr τ wj qj ↔
            coef P i Cs Cr τ < coef P j Cs Cr τ) := by sorry

end SupplyChainFactoring.Choice
