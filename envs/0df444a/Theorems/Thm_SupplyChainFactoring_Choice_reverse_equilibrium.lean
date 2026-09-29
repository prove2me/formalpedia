-- Prove2me | Theorems.Thm_SupplyChainFactoring_Choice_reverse_equilibrium
-- name    : SupplyChainFactoring.Choice.reverse_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:24:53.017113+00:00
-- url     : https://prove2.me/theorems/0aaf5232-87a5-4ad6-8695-79cf7e25b36b
-- title:
--   §5.2 (Proposition EC.2) — reverse factoring is feasible iff $C_s > \mathbb C_{\mathcal R}$, with a unique equilibrium
-- statement:
--   Fix the model data and demand of the definitions, a retailer rating $C_r \in (C_{\min}, C_{\max})$ and a payment extension $\tau \ge 0$, and let $\mathbb C_{\mathcal R}$ be the unique value of $C_s \in (C_{\min}, C_{\max})$ that satisfies $c_{\mathcal R}(\tau) = p$, where $c_{\mathcal R}(\tau) = c\,e^{(\eta_s+\lambda_s)t_1+\eta_r(t_2+\tau)}$. Then for every supplier rating $C_s \in (C_{\min}, C_{\max})$:
--
--   1. reverse factoring is feasible if and only if $C_s > \mathbb C_{\mathcal R}$;
--   2. if $C_s > \mathbb C_{\mathcal R}$, the reverse-factoring game, in which the retailer's profit is $\Pi_{\mathcal R}(w, \tau) = e^{-\lambda_s t_1}(1-\rho_r)(2 - e^{-\lambda_r \tau})(p-w)S(q)$, has exactly one equilibrium $(w^*_{\mathcal R}, q^*_{\mathcal R})$, and $(w, q)$ is that equilibrium if and only if $0 < q < \mathbb Z$ and
--
--   $$p\bar F(q) = c_{\mathcal R}(\tau)\,[1 + z(q)k(q)], \qquad w = \frac{c_{\mathcal R}(\tau)}{\bar F(q)}.$$
--
--   The equilibrium of reverse factoring thus has the same form as under factoring, with effective unit cost $c_{\mathcal R}(\tau)$.
--
--   **Formalization Note** The paper writes that the unique equilibrium "preserves the similar fashion as in factorings, with a different effective unit production cost $c_{\mathcal R}(\tau)$"; this is read as the system of Propositions 2–3 with $c_{\mathcal R}(\tau)$ in place of $c_{\mathcal F}$, $c_{\mathcal N}$. The retailer's factor $2 - e^{-\lambda_r \tau}$ is kept in the retailer's profit, as printed on the last line of the p. 6082 display.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6082, §5.2 (Proposition EC.2 of Online Appendix B), with Eq. (12)

import Mathlib
import Definitions.Def_SupplyChainFactoring_Choice_Demand
import Definitions.Def_SupplyChainFactoring_Choice_Model

open MeasureTheory Real

namespace SupplyChainFactoring.Choice

/-- Kouvelis–Xu 2021, §5.2 (p. 6082; Proposition EC.2 of the Online Appendix). For a given
payment extension `τ ≥ 0`, with `ℂ_𝓡` the unique supplier rating at which `c_𝓡(τ) = p`: reverse
factoring is feasible iff `Cs > ℂ_𝓡`, and under feasibility the unique equilibrium is characterized
as under factoring, with the effective unit cost `c_𝓡(τ)`. -/
theorem reverse_equilibrium (P : Params) (hP : P.Valid) (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal)
    (hD : DemandModel μ f Z) (Cr : ℝ) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (τ : ℝ) (hτ : 0 ≤ τ) (CR : ℝ) (hCR : IsUniqueSolution P.Cmin P.Cmax (fun Cs => cR P Cs Cr τ = P.p) CR) :
    ∀ Cs ∈ Set.Ioo P.Cmin P.Cmax,
      (Feasible P μ .reverse Cs Cr τ ↔ CR < Cs) ∧
      (CR < Cs →
        (∃! e : ℝ × ℝ, IsEquilibrium P μ .reverse Cs Cr τ e.1 e.2) ∧
        ∀ w q : ℝ, IsEquilibrium P μ .reverse Cs Cr τ w q ↔
          (0 < q ∧ (q : EReal) < Z ∧
            P.p * Fbar μ q = cR P Cs Cr τ * (1 + z μ f q * k μ q) ∧
            w = cR P Cs Cr τ / Fbar μ q)) := by sorry

end SupplyChainFactoring.Choice
