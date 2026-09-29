-- Prove2me | Theorems.Thm_SupplyChainFactoring_Choice_financing_choice_given_extension
-- name    : SupplyChainFactoring.Choice.financing_choice_given_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:26:35.123774+00:00
-- url     : https://prove2.me/theorems/70f1ec9e-c8f2-4477-93a8-44d91ca51dd6
-- title:
--   Proposition 5 — the supplier's choice among recourse, non-recourse and reverse factoring for a given payment extension
-- statement:
--   Fix the model data and demand of the definitions, a retailer rating $C_r \in (C_{\min}, C_{\max})$ and a payment extension $\tau \ge 0$. Let $\mathbb C_{\mathcal F}$, $\mathbb C_{\mathcal N}$, $\mathbb C_{\mathcal R}$ be the feasibility thresholds of recourse, non-recourse and reverse factoring, $\mathbb C_1$ the threshold of Proposition 4, and $\mathbb C_3$ the unique value of $C_s \in (C_{\min}, C_{\max})$ that satisfies
--
--   $$(1-\rho_r) + (1-\rho_s) - e^{\eta_s t_2} = e^{-\eta_r(t_2+\tau)}.$$
--
--   Let all three schemes be available to the supplier. Then for every supplier rating $C_s \in (C_{\min}, C_{\max})$:
--
--   1. if $C_r > \mathbb C_2$, that is $e^{-\eta_r \tau} < 1 - \rho_r$, then recourse factoring is adopted iff $C_s > \mathbb C_{\mathcal F} \vee \mathbb C_1$, and non-recourse factoring is adopted iff $\mathbb C_{\mathcal N} < C_s \le \mathbb C_1$;
--   2. if $C_r \le \mathbb C_2$, that is $1 - \rho_r \le e^{-\eta_r \tau}$, then recourse factoring is adopted iff $C_s > \mathbb C_{\mathcal F} \vee \mathbb C_3$, and reverse factoring is adopted iff $\mathbb C_{\mathcal R} < C_s \le \mathbb C_3$.
--
--   Here $\vee$ is the maximum. Reverse factoring can thus be dominated by non-recourse factoring when the retailer's rating is high relative to the payment extension; when it is adopted, it is adopted by suppliers with low (but feasible) to medium ratings.
--
--   **Formalization Note** The paper introduces $\mathbb C_2$ as "the unique value of $C_r$ that satisfies $1 - \rho_r = e^{-\eta_r \tau}$". Both sides increase in $C_r$, so the stated assumptions do not give a single crossing (and for $\tau = 0$ there is no solution in $(C_{\min}, C_{\max})$). The two cases are therefore stated through the paper's own equivalent form (p. 6083: "the condition $C_r > \mathbb C_2$, which is equivalent to $\tau > -\eta_r^{-1}\ln(1-\rho_r)$"), i.e. $e^{-\eta_r \tau} < 1 - \rho_r$ and its negation. "Adopted" is the predicate `Adopted` with available set $\{\mathcal F, \mathcal N, \mathcal R\}$ and tie order $\mathcal R \succ \mathcal N \succ \mathcal F$. Part (ii) says nothing about non-recourse factoring, and no clause about it is added. The thresholds enter by their defining equations and uniqueness (the one for $\mathbb C_{\mathcal F}$ cross-multiplied), and all five are hypotheses of both cases.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6083, Proposition 5 (and the reading of C_r > ℂ_2 in the paragraph after it)

import Mathlib
import Definitions.Def_SupplyChainFactoring_Choice_Demand
import Definitions.Def_SupplyChainFactoring_Choice_Model

open MeasureTheory Real

namespace SupplyChainFactoring.Choice

/-- Kouvelis–Xu 2021, Proposition 5 (p. 6083). For a given payment extension `τ ≥ 0`, with all
three schemes available, and `ℂ_3` the unique supplier rating with
`Λ_𝓕(Cs, Cr) = Λ_𝓡 = e^{−η_r(t2+τ)}`:
(i) if `C_r > ℂ_2`, read as `e^{−η_r τ} < 1 − ρ_r` (the paper's equivalent form
`τ > −η_r⁻¹ ln(1 − ρ_r)`, p. 6083), recourse factoring is adopted iff `Cs > ℂ_𝓕 ∨ ℂ_1` and
non-recourse factoring is adopted iff `ℂ_𝓝 < Cs ≤ ℂ_1`;
(ii) if `C_r ≤ ℂ_2`, i.e. `1 − ρ_r ≤ e^{−η_r τ}`, recourse factoring is adopted iff
`Cs > ℂ_𝓕 ∨ ℂ_3` and reverse factoring is adopted iff `ℂ_𝓡 < Cs ≤ ℂ_3`. -/
theorem financing_choice_given_extension (P : Params) (hP : P.Valid) (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal)
    (hD : DemandModel μ f Z) (Cr : ℝ) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (τ : ℝ) (hτ : 0 ≤ τ) (CF : ℝ) (hCF : IsUniqueSolution P.Cmin P.Cmax
      (fun Cs => P.c * exp ((P.η Cs + P.lamS) * P.t1) = P.p * coefF P Cs Cr) CF)
    (CN : ℝ) (hCN : IsUniqueSolution P.Cmin P.Cmax (fun Cs => cN P Cs Cr = P.p) CN)
    (CR : ℝ) (hCR : IsUniqueSolution P.Cmin P.Cmax (fun Cs => cR P Cs Cr τ = P.p) CR)
    (C1 : ℝ) (hC1 : IsUniqueSolution P.Cmin P.Cmax (fun Cs => coefF P Cs Cr = coefN P Cr) C1)
    (C3 : ℝ) (hC3 : IsUniqueSolution P.Cmin P.Cmax (fun Cs => coefF P Cs Cr = coefR P Cr τ) C3) :
    ∀ Cs ∈ Set.Ioo P.Cmin P.Cmax,
      (exp (-(P.η Cr * τ)) < 1 - P.ρ Cr →
        (Adopted P μ Set.univ .recourse Cs Cr τ ↔ max CF C1 < Cs) ∧
        (Adopted P μ Set.univ .nonRecourse Cs Cr τ ↔ CN < Cs ∧ Cs ≤ C1)) ∧
      (1 - P.ρ Cr ≤ exp (-(P.η Cr * τ)) →
        (Adopted P μ Set.univ .recourse Cs Cr τ ↔ max CF C3 < Cs) ∧
        (Adopted P μ Set.univ .reverse Cs Cr τ ↔ CR < Cs ∧ Cs ≤ C3)) := by sorry

end SupplyChainFactoring.Choice
