-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_proposition_3_2
-- name    : PolymerEndpoint.Atomic.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:59.29706+00:00
-- url     : https://prove2.me/theorems/5d63889a-c1f0-4fd5-9e18-bfbe3852de91
-- title:
--   Proposition 3.2 — continuity of the update law and log moments
-- statement:
--   Assume the standing disorder and moment conditions. If partitioned states $f_n$ converge to $g$ in $d$, then their updated laws converge in the Wasserstein distance:
--   $$
--   \mathcal W(\mathcal T f_n,\mathcal T g)\longrightarrow0.
--   $$
--   For every positive integer $q$, the $q$th log moment of the update denominator also converges:
--   $$
--   \mathbb E[(\log\widetilde F(f_n))^q]\longrightarrow\mathbb E[(\log\widetilde F(g))^q].
--   $$
--
--   The case $q=1$ supplies continuity of the energy functional $R$. The result controls both the stochastic update and its variational cost.
--
--   **Formalization Note** The standing range is $\beta>0$ (§1.1). The disorder law is non-degenerate and satisfies (1.1) on $[-2\beta,2\beta]$; $d\geq1$.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, pp. 28–29, Proposition 3.2

import Definitions.Def_PolymerEndpoint_Atomic_Update

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace PolymerEndpoint.Atomic

theorem proposition_3_2 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 < β) (hmom : MomentCondition 𝔏 β) :
    (∀ (f : ℕ → PSM d) (g : PSM d),
      Tendsto (fun n => dist (f n) g) atTop (𝓝 0) →
      Tendsto (fun n => W (T 𝔏 β (f n)) (T 𝔏 β g)) atTop (𝓝 0)) ∧
    (∀ q : ℕ, 1 ≤ q → ∀ (f : ℕ → PSM d) (g : PSM d),
      Tendsto (fun n => dist (f n) g) atTop (𝓝 0) →
      Tendsto (fun n => ∫ Y, (Real.log (Ftil 𝔏 β (f n) Y)) ^ q
          ∂(envLaw (d := d) 𝔏)) atTop
        (𝓝 (∫ Y, (Real.log (Ftil 𝔏 β g Y)) ^ q
          ∂(envLaw (d := d) 𝔏)))) := by sorry

end PolymerEndpoint.Atomic
