-- Prove2me | Theorems.Thm_SupplyChainFactoring_Choice_factoring_choice
-- name    : SupplyChainFactoring.Choice.factoring_choice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:26:02.445535+00:00
-- url     : https://prove2.me/theorems/cf83e9bc-78c7-4772-927e-a303bb8725ed
-- title:
--   Proposition 4 — the supplier's choice between recourse and non-recourse factoring
-- statement:
--   Fix the model data and demand of the definitions and a retailer rating $C_r \in (C_{\min}, C_{\max})$. Let $\mathbb C_{\mathcal F}$ and $\mathbb C_{\mathcal N}$ be the feasibility thresholds of Propositions 2 and 3, and let $\mathbb C_1$ be the unique value of $C_s \in (C_{\min}, C_{\max})$ that satisfies
--
--   $$(1-\rho_r) + (1-\rho_s) - e^{\eta_s t_2} = e^{-\eta_r t_2}(1-\rho_r).$$
--
--   When both factoring schemes, and only they, are available to the supplier ($A = \{\mathcal F, \mathcal N\}$), then for every supplier rating $C_s \in (C_{\min}, C_{\max})$:
--
--   1. non-recourse factoring is adopted if and only if $\mathbb C_{\mathcal N} < C_s \le \mathbb C_1$;
--   2. recourse factoring is adopted if and only if $C_s > \mathbb C_{\mathcal F} \vee \mathbb C_1$, where $\vee$ denotes the maximum.
--
--   Non-recourse factoring is thus the choice of suppliers with medium ratings, recourse factoring that of suppliers with high ratings.
--
--   **Formalization Note** The paper writes "should be adopted"; this is read as the predicate `Adopted` (feasible, and best equilibrium supplier profit with ties resolved $\mathcal N \succ \mathcal F$, as the paper's boundary $C_s = \mathbb C_1$ requires). No ordering between $\mathbb C_{\mathcal F}$, $\mathbb C_{\mathcal N}$, $\mathbb C_1$ is assumed; an empty interval is allowed. The payment extension $\tau$ is a dummy argument, since reverse factoring is not available.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, p. 6080, Proposition 4

import Mathlib
import Definitions.Def_SupplyChainFactoring_Choice_Demand
import Definitions.Def_SupplyChainFactoring_Choice_Model

open MeasureTheory Real

namespace SupplyChainFactoring.Choice

/-- Kouvelis–Xu 2021, Proposition 4 (p. 6080). Let `ℂ_1` be the unique supplier rating with
`Λ_𝓕(Cs, Cr) = Λ_𝓝(Cr)`. When both factoring schemes (and only they) are available:
(i) non-recourse factoring is adopted iff `ℂ_𝓝 < Cs ≤ ℂ_1`;
(ii) recourse factoring is adopted iff `Cs > ℂ_𝓕 ∨ ℂ_1`, where `∨` is the maximum. -/
theorem factoring_choice (P : Params) (hP : P.Valid) (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal)
    (hD : DemandModel μ f Z) (Cr : ℝ) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (τ : ℝ) (CF : ℝ) (hCF : IsUniqueSolution P.Cmin P.Cmax
      (fun Cs => P.c * exp ((P.η Cs + P.lamS) * P.t1) = P.p * coefF P Cs Cr) CF)
    (CN : ℝ) (hCN : IsUniqueSolution P.Cmin P.Cmax (fun Cs => cN P Cs Cr = P.p) CN)
    (C1 : ℝ) (hC1 : IsUniqueSolution P.Cmin P.Cmax (fun Cs => coefF P Cs Cr = coefN P Cr) C1) :
    ∀ Cs ∈ Set.Ioo P.Cmin P.Cmax,
      (Adopted P μ {Scheme.recourse, Scheme.nonRecourse} .nonRecourse Cs Cr τ ↔
          CN < Cs ∧ Cs ≤ C1) ∧
      (Adopted P μ {Scheme.recourse, Scheme.nonRecourse} .recourse Cs Cr τ ↔
          max CF C1 < Cs) := by sorry

end SupplyChainFactoring.Choice
