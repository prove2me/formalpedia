-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_theorem_4_7
-- name    : PolymerEndpoint.Atomic.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:42.730362+00:00
-- url     : https://prove2.me/theorems/3daa7190-3e89-49c9-b1fa-b09a2c0ef227
-- title:
--   Theorem 4.7 — variational formula: $\lim F_n=\inf_{\nu\in\mathcal K}\mathcal R(\nu)$ a.s.
-- statement:
--   Throughout, $d\geq1$; the disorder law $\mathfrak L$ is a non-degenerate probability measure on $\mathbb R$ with $\lambda(\alpha)=\log\mathbb E e^{\alpha X}<\infty$ for all $\alpha\in[-2\beta,2\beta]$ (the paper's (1.1)). Let $\beta>0$ and let $(X_u)$ be an i.i.d. environment with law $\mathfrak L$. Let $\mathcal K$ be the set of fixed points of the update map (4.5), $\mathcal R$ the energy functional (4.6) and $\mathbf 1\in\mathcal S$ the class of unit point masses. Then
--
--   1. $\displaystyle\limsup_{n\to\infty}\mathbb E(F_n)\leq\inf_{\nu\in\mathcal K}\mathcal R(\nu)$;
--   2. $\displaystyle\lim_{n\to\infty}F_n=\inf_{\nu\in\mathcal K}\mathcal R(\nu)$ almost surely (4.13);
--   3. the minimum value satisfies (4.14):
--
--   $$
--   \inf_{\nu\in\mathcal K}\mathcal R(\nu)=\lim_{n\to\infty}\frac1n\sum_{i=0}^{n-1}\mathcal R(\mathcal T^i\delta_{\mathbf 1}).
--   $$
--
--   This expresses the limiting free energy $p(\beta)$ as the minimum of an energy functional over the fixed points of $\mathcal T$, which is how the phase of the polymer is read off the fixed-point set.
--
--   **Formalization Note** The infimum is taken over the subtype $\mathcal K$. Clause 1 is written in its elementary form (for every $c>\inf_{\mathcal K}\mathcal R$, eventually $\mathbb E F_n<c$). $\mathbb E(F_n)$ is computed on the canonical product environment. The standing range is $\beta>0$ (§1.1).
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 35, Theorem 4.7, (4.13)–(4.14)

import Definitions.Def_PolymerEndpoint_Atomic_Update

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

theorem theorem_4_7 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 < β) (hmom : MomentCondition 𝔏 β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Cell d → Ω → ℝ)
    (henv : IsEnvironment X 𝔏 P) :
    (∀ c : ℝ, (⨅ ν : K (d := d) 𝔏 β, RR 𝔏 β (ν : Measure (PSM d))) < c →
      ∀ᶠ n : ℕ in atTop, meanF (d := d) 𝔏 β n < c) ∧
    (∀ᵐ a ∂P, Tendsto (fun n : ℕ => F X β n a) atTop
      (𝓝 (⨅ ν : K (d := d) 𝔏 β, RR 𝔏 β (ν : Measure (PSM d))))) ∧
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        RR 𝔏 β ((Tlift 𝔏 β)^[i] (Measure.dirac (one (d := d))))) atTop
      (𝓝 (⨅ ν : K (d := d) 𝔏 β, RR 𝔏 β (ν : Measure (PSM d)))) := by sorry

end PolymerEndpoint.Atomic
