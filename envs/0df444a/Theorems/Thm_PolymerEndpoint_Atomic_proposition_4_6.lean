-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_proposition_4_6
-- name    : PolymerEndpoint.Atomic.proposition_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:10.821574+00:00
-- url     : https://prove2.me/theorems/b3490973-3ea6-4f3e-a849-21fd5183eb35
-- title:
--   Proposition 4.6 — $\liminf F_n\ge\inf_{\mathcal K}\mathcal R$ a.s. and $\liminf\mathbb E F_n\ge\inf_{\mathcal K}\mathcal R$
-- statement:
--   Throughout, $d\geq1$; the disorder law $\mathfrak L$ is a non-degenerate probability measure on $\mathbb R$ with $\lambda(\alpha)=\log\mathbb E e^{\alpha X}<\infty$ for all $\alpha\in[-2\beta,2\beta]$ (the paper's (1.1)). Let $\beta>0$ and let $(X_u)$ be an i.i.d. environment with law $\mathfrak L$. Let $\mathcal K$ be the set of fixed points of the update map (4.5) and $\mathcal R$ the energy functional (4.6). Then
--
--   $$
--   \liminf_{n\to\infty}F_n\geq\inf_{\nu\in\mathcal K}\mathcal R(\nu)\quad\text{a.s.},\qquad
--   \liminf_{n\to\infty}\mathbb E(F_n)\geq\inf_{\nu\in\mathcal K}\mathcal R(\nu).
--   $$
--
--   These are the lower halves of the variational formula for the free energy (Theorem 4.7).
--
--   **Formalization Note** A lower bound on a $\liminf$ is written in its elementary form: for every $c<\inf_{\mathcal K}\mathcal R$, eventually $c<F_n$ (resp. $c<\mathbb E F_n$). The infimum is taken over the subtype $\mathcal K$. $\mathbb E(F_n)$ is computed on the canonical product environment, which has the same law. The standing range is $\beta>0$ (§1.1).
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 34, Proposition 4.6, (4.9)–(4.10)

import Definitions.Def_PolymerEndpoint_Atomic_Update

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

theorem proposition_4_6 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 < β) (hmom : MomentCondition 𝔏 β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Cell d → Ω → ℝ)
    (henv : IsEnvironment X 𝔏 P) :
    (∀ᵐ a ∂P, ∀ c : ℝ, c < (⨅ ν : K (d := d) 𝔏 β, RR 𝔏 β (ν : Measure (PSM d))) →
      ∀ᶠ n : ℕ in atTop, c < F X β n a) ∧
    (∀ c : ℝ, c < (⨅ ν : K (d := d) 𝔏 β, RR 𝔏 β (ν : Measure (PSM d))) →
      ∀ᶠ n : ℕ in atTop, c < meanF (d := d) 𝔏 β n) := by sorry

end PolymerEndpoint.Atomic
