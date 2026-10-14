-- Prove2me | Theorems.Thm_QuantileSPQO_Rate_lemma_1
-- name    : QuantileSPQO.Rate.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:57.757612+00:00
-- url     : https://prove2.me/theorems/d8d73d7e-bb04-4c41-918e-8b851d56d5a0
-- title:
--   Lemma 1 — under A1, A2, A3(a): sup_k E‖D_k‖² < ∞ and sup_k ‖D_k‖ < ∞ w.p.1
-- statement:
--   Let $(\theta_k,q_k,D_k)$ be a run of Algorithm SPQO on a probability space $(\Omega,P)$ with filtration $(\mathcal F_k)$, for a black box with quantile function $q$ on a constraint set $\Theta\subseteq\mathbb R^d$, $d\ge1$, with $\Pi_\Theta$ the Euclidean projection onto $\Theta$. Assume A1, A2 and A3(a). Then
--
--   1. $\displaystyle\sup_k E\big[\|D_k\|^2\big]<\infty$;
--   2. $\displaystyle\sup_k\|D_k\|<\infty$ almost surely.
--
--   Lemma 1 is what keeps the adaptive perturbation $\bar c_k$ and the gradient tracker under control; it feeds Lemma 2, Theorem 1 and the rate analysis.
--
--   **Formalization Note** The run, A1, A2 and A3(a) are those of the Setting file (with the disclosures there: truncated quantile step, A1's first-derivative bound, conditional-marginal sampling model, $\theta_0\in\Theta$). The expectation is a Lebesgue integral in $[0,\infty]$, so part (i) asserts finiteness and never relies on integrability.
-- source:
--   Hu, Song and Fu, Quantile Optimization via Multiple Timescale Local Search for Black-box Functions, arXiv:2308.07607v1, p. 13, Lemma 1

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace QuantileSPQO.Rate

theorem lemma_1 {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c) :
    (⨆ k, ∫⁻ ω, ‖R.D k ω‖ₑ ^ 2 ∂P) < ⊤ ∧
      ∀ᵐ ω ∂P, BddAbove (Set.range fun k => ‖R.D k ω‖) := by sorry

end QuantileSPQO.Rate
