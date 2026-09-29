-- Prove2me | Theorems.Thm_SupplyChainFactoring_Choice_nonRecourse_equilibrium
-- name    : SupplyChainFactoring.Choice.nonRecourse_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:24:08.631281+00:00
-- url     : https://prove2.me/theorems/4ca26be3-4d1d-42d0-8f7e-57fa821befea
-- title:
--   Proposition 3 — non-recourse factoring is feasible iff $C_s > \mathbb C_{\mathcal N}$, with a unique equilibrium
-- statement:
--   Fix the model data and demand of the definitions, a retailer rating $C_r \in (C_{\min}, C_{\max})$, and let $\mathbb C_{\mathcal N}$ be the unique value of $C_s \in (C_{\min}, C_{\max})$ that satisfies $c_{\mathcal N} = p$, where $c_{\mathcal N} = c\,e^{(\eta_s+\lambda_s)t_1+\eta_r t_2}/(1-\rho_r)$. Then for every supplier rating $C_s \in (C_{\min}, C_{\max})$:
--
--   1. non-recourse factoring is feasible if and only if $C_s > \mathbb C_{\mathcal N}$;
--   2. if $C_s > \mathbb C_{\mathcal N}$, the non-recourse game has exactly one equilibrium $(w^*_{\mathcal N}, q^*_{\mathcal N})$, and a pair $(w, q)$ is that equilibrium if and only if $0 < q < \mathbb Z$ and
--
--   $$p\bar F(q) = c_{\mathcal N}\,[1 + z(q)k(q)], \qquad w = \frac{c_{\mathcal N}}{\bar F(q)}.$$
--
--   Non-recourse factoring transfers the demand risk and the retailer's credit risk to the factor; its financing cost depends on the supplier's rating only through the premium $\eta_s$ of the bank loan.
--
--   **Formalization Note** $c_{\mathcal N}$ depends on $C_s$ only through $\eta_s$, which is only weakly decreasing, so the uniqueness of $\mathbb C_{\mathcal N}$ is a genuine hypothesis (the paper's "the unique value"). Part (ii) is read under feasibility, as for Proposition 2. The payment extension $\tau$ is a dummy argument.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6079, Proposition 3 (with Eq. (9))

import Mathlib
import Definitions.Def_SupplyChainFactoring_Choice_Demand
import Definitions.Def_SupplyChainFactoring_Choice_Model

open MeasureTheory Real

namespace SupplyChainFactoring.Choice

/-- Kouvelis–Xu 2021, Proposition 3 (p. 6079). With `ℂ_𝓝` the unique supplier rating at which
`c_𝓝 = p`: (i) non-recourse factoring is feasible iff `Cs > ℂ_𝓝`; (ii) under feasibility the
equilibrium exists, is unique, and is characterized by `p F̄(q) = c_𝓝 [1 + z(q) k(q)]`,
`w = c_𝓝 / F̄(q)` with `q ∈ (0, Z)`. The payment extension `τ` plays no role here. -/
theorem nonRecourse_equilibrium (P : Params) (hP : P.Valid) (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal)
    (hD : DemandModel μ f Z) (Cr : ℝ) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (τ : ℝ) (CN : ℝ) (hCN : IsUniqueSolution P.Cmin P.Cmax (fun Cs => cN P Cs Cr = P.p) CN) :
    ∀ Cs ∈ Set.Ioo P.Cmin P.Cmax,
      (Feasible P μ .nonRecourse Cs Cr τ ↔ CN < Cs) ∧
      (CN < Cs →
        (∃! e : ℝ × ℝ, IsEquilibrium P μ .nonRecourse Cs Cr τ e.1 e.2) ∧
        ∀ w q : ℝ, IsEquilibrium P μ .nonRecourse Cs Cr τ w q ↔
          (0 < q ∧ (q : EReal) < Z ∧
            P.p * Fbar μ q = cN P Cs Cr * (1 + z μ f q * k μ q) ∧
            w = cN P Cs Cr / Fbar μ q)) := by sorry

end SupplyChainFactoring.Choice
