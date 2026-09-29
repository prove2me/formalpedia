-- Prove2me | Theorems.Thm_SupplyChainFactoring_Choice_recourse_equilibrium
-- name    : SupplyChainFactoring.Choice.recourse_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:23:40.397824+00:00
-- url     : https://prove2.me/theorems/a44b3463-7461-4fb1-84b1-0273e6d8b893
-- title:
--   Proposition 2 — recourse factoring is feasible iff $C_s > \mathbb C_{\mathcal F}$, with a unique equilibrium
-- statement:
--   Fix the model data and demand of the definitions (strictly IFR demand with support end $\mathbb Z$), a retailer rating $C_r \in (C_{\min}, C_{\max})$, and let $\mathbb C_{\mathcal F}$ be the unique value of $C_s \in (C_{\min}, C_{\max})$ that satisfies $c_{\mathcal F} = p$. Then for every supplier rating $C_s \in (C_{\min}, C_{\max})$:
--
--   1. recourse factoring is feasible if and only if $C_s > \mathbb C_{\mathcal F}$;
--   2. if $C_s > \mathbb C_{\mathcal F}$, the recourse-factoring game has exactly one equilibrium $(w^*_{\mathcal F}, q^*_{\mathcal F})$, and a pair $(w, q)$ is that equilibrium if and only if $0 < q < \mathbb Z$ and
--
--   $$p\bar F(q) = c_{\mathcal F}\,[1 + z(q)k(q)], \qquad w = \frac{c_{\mathcal F}}{\bar F(q)}.$$
--
--   The threshold $\mathbb C_{\mathcal F}$ is the **feasibility threshold** of recourse factoring: only suppliers with relatively high credit ratings can use it.
--
--   **Formalization Note** Because $\Lambda_{\mathcal F}$ can be $\le 0$, the defining equation $c_{\mathcal F} = p$ of $\mathbb C_{\mathcal F}$ is stated cross-multiplied, $c\,e^{(\eta_s+\lambda_s)t_1} = p\,\Lambda_{\mathcal F}(C_s, C_r)$. Part (ii) is read under the feasibility condition of part (i) (it has no content otherwise). "Can be derived from" is read as: the equilibrium exists, is unique, and the pairs solving the system with $q \in (0, \mathbb Z)$ are exactly the equilibria. The payment extension $\tau$ is a dummy argument here.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6078, Proposition 2 (with Eq. (8))

import Mathlib
import Definitions.Def_SupplyChainFactoring_Choice_Demand
import Definitions.Def_SupplyChainFactoring_Choice_Model

open MeasureTheory Real

namespace SupplyChainFactoring.Choice

/-- Kouvelis–Xu 2021, Proposition 2 (p. 6078). With `ℂ_𝓕` the unique supplier rating at which
`c_𝓕 = p` (stated cross-multiplied, `c e^{(η_s+λ_s)t1} = p Λ_𝓕`): (i) recourse factoring is
feasible iff `Cs > ℂ_𝓕`; (ii) under feasibility the equilibrium exists, is unique, and is
characterized by `p F̄(q) = c_𝓕 [1 + z(q) k(q)]`, `w = c_𝓕 / F̄(q)` with `q ∈ (0, Z)`.
The payment extension `τ` plays no role under recourse factoring. -/
theorem recourse_equilibrium (P : Params) (hP : P.Valid) (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal)
    (hD : DemandModel μ f Z) (Cr : ℝ) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (τ : ℝ) (CF : ℝ) (hCF : IsUniqueSolution P.Cmin P.Cmax
      (fun Cs => P.c * exp ((P.η Cs + P.lamS) * P.t1) = P.p * coefF P Cs Cr) CF) :
    ∀ Cs ∈ Set.Ioo P.Cmin P.Cmax,
      (Feasible P μ .recourse Cs Cr τ ↔ CF < Cs) ∧
      (CF < Cs →
        (∃! e : ℝ × ℝ, IsEquilibrium P μ .recourse Cs Cr τ e.1 e.2) ∧
        ∀ w q : ℝ, IsEquilibrium P μ .recourse Cs Cr τ w q ↔
          (0 < q ∧ (q : EReal) < Z ∧
            P.p * Fbar μ q = cF P Cs Cr * (1 + z μ f q * k μ q) ∧
            w = cF P Cs Cr / Fbar μ q)) := by sorry

end SupplyChainFactoring.Choice
