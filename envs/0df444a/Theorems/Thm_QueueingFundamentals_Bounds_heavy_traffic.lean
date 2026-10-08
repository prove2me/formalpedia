-- Prove2me | Theorems.Thm_QueueingFundamentals_Bounds_heavy_traffic
-- name    : QueueingFundamentals.Bounds.heavy_traffic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:34:36.295235+00:00
-- url     : https://prove2.me/theorems/34b5d7cc-de24-4099-b5c1-56ce57f16f41
-- title:
--   Theorem 7.1 — heavy traffic, $(2\alpha_j/\beta_j^2)\,W_{q,j} \to_d \mathrm{Exp}(1)$
-- statement:
--   Consider a sequence of G/G/1 queues indexed by $j$. Queue $j$ has a nonnegative interarrival time $T_j$ with law $A_j$ and a nonnegative service time $S_j$ with law $B_j$, both with finite second moments. Its rates are $\lambda_j = 1/E[T_j] > 0$ and $\mu_j = 1/E[S_j] > 0$, and its traffic intensity is $\rho_j = \lambda_j/\mu_j < 1$. Let $W_{q,j}$ have a stationary law $\nu_j$ of the line delay under queue $j$'s Lindley recursion, and write
--   $$
--   \alpha_j = -E[S_j - T_j], \qquad \beta_j^2 = \mathrm{Var}[S_j - T_j],
--   $$
--   with $S_j$ and $T_j$ independent. Suppose that:
--   1. $T_j \to_d T$ and $S_j \to_d S$ (convergence in distribution), and $\rho_j \to 1$;
--   2. (a) $\mathrm{Var}[S - T] > 0$ for independent $S$ and $T$;
--   3. (b) for some $\delta > 0$ and some constant $C$, $E[S_j^{2+\delta}] < C$ and $E[T_j^{2+\delta}] < C$ for all $j$.
--
--   Then
--   $$
--   \frac{2\alpha_j}{\beta_j^2}\, W_{q,j} \ \to_d\ \mathrm{Exp}(1).
--   $$
--
--   Near saturation the stationary queue wait is therefore approximately exponential with mean $\beta_j^2/(2\alpha_j)$. The book states this theorem without proof.
--
--   **Formalization Note** "$W_{q,j}$ in steady state" is modelled by a stationary law $\nu_j$ for each $j$, taken as a hypothesis. Convergence in distribution means convergence of $\int g$ for every bounded continuous $g$. The moments in (b) are stated as integrable with integral below $C$. $\mathrm{Exp}(1)$ is Mathlib's `expMeasure 1`.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.350, Theorem 7.1

import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Theorem 7.1, p.350 (heavy traffic). A sequence of G/G/1 queues indexed by `j`, queue `j`
with interarrival law `A j` (of `T_j`), service law `B j` (of `S_j`), rates `λ_j, μ_j`,
`ρ_j = λ_j/μ_j < 1`, and stationary line-delay law `ν j` (of `W_{q,j}`). Let
`α_j = −E[S_j − T_j]`, `β_j² = Var[S_j − T_j]`. If `T_j →d T`, `S_j →d S`, `ρ_j → 1`,
(a) `Var[S − T] > 0`, and (b) for some `δ > 0` and some constant `C`, `E[S_j^{2+δ}] < C` and
`E[T_j^{2+δ}] < C` for all `j`, then `(2α_j/β_j²) W_{q,j} →d Exp(1)`. -/
theorem heavy_traffic
    (A B ν : ℕ → Measure ℝ) (lam mu : ℕ → ℝ) (Alim Blim : Measure ℝ)
    [IsProbabilityMeasure Alim] [IsProbabilityMeasure Blim]
    (hlam : ∀ j, 0 < lam j) (hmu : ∀ j, 0 < mu j)
    (hin : ∀ j, IsGG1Input (A j) (B j) (lam j) (mu j))
    (hrho : ∀ j, lam j / mu j < 1)
    (hν : ∀ j, IsStationaryWaitLaw (A j) (B j) (ν j))
    (hA : ConvergesInDistribution A Alim) (hB : ConvergesInDistribution B Blim)
    (hrho1 : Tendsto (fun j => lam j / mu j) atTop (𝓝 1))
    (ha : 0 < variance (fun p : ℝ × ℝ => p.1 - p.2) (Blim.prod Alim))
    (hb : ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ j,
      (Integrable (fun x : ℝ => |x| ^ (2 + δ)) (B j) ∧ ∫ x, |x| ^ (2 + δ) ∂(B j) < C) ∧
      (Integrable (fun x : ℝ => |x| ^ (2 + δ)) (A j) ∧ ∫ x, |x| ^ (2 + δ) ∂(A j) < C)) :
    ConvergesInDistribution
      (fun j => (ν j).map (fun w : ℝ =>
        (2 * (-∫ p, (p.1 - p.2) ∂((B j).prod (A j))) /
          variance (fun p : ℝ × ℝ => p.1 - p.2) ((B j).prod (A j))) * w))
      (expMeasure 1) := by sorry

end QueueingFundamentals.Bounds
