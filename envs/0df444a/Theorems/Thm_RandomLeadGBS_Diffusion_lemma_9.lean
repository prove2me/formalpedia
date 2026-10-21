-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_lemma_9
-- name    : RandomLeadGBS.Diffusion.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:53.622484+00:00
-- url     : https://prove2.me/theorems/20a3c180-f240-4297-8519-c5fa6cf6e9f5
-- title:
--   Lemma 9, pp. 22–23 — A_r ⇒ A with E A_r^± → E A^±, A_r ≤st B_r and EB_r − EA_r → 0 imply B_r ⇒ A and E B_r^± → E A^±
-- statement:
--   Let $(A_r)$ and $(B_r)$, $r\to\infty$, be real random variables with laws $\mu_r$ and $\nu_r$, and let $A$ have law $\mu_A$ (all probability measures on $\mathbb R$). Suppose
--
--   1. $A_r\Rightarrow A$, (32)
--   2. $\mathbb E|A|<\infty$, and $\mathbb E A_r^+\to\mathbb E A^+$, $\mathbb E A_r^-\to\mathbb E A^-$, (33)
--   3. $A_r\le_{st}B_r$ for every positive $r$, i.e. $\mathbb P\{A_r>x\}\le\mathbb P\{B_r>x\}$ for all real $x$,
--   4. $\mathbb E B_r - \mathbb E A_r \to 0$.
--
--   Then
--   $$
--   B_r\Rightarrow A, \tag{34}
--   $$
--   $$
--   \mathbb E B_r^+\to\mathbb E A^+,\qquad \mathbb E B_r^-\to\mathbb E A^-. \tag{35}
--   $$
--   This transfer lemma moves the limit of Lemma 5 from the artificial chain to the GBS chain once (36) is shown.
--
--   **Formalization Note** The index $r$ runs to $\infty$ through the positive reals. Weak convergence is stated as convergence of $\int g$ for every bounded continuous $g$. The means $\mathbb E A_r$ and $\mathbb E B_r$ appear in hypothesis 4, so $A_r$ and $B_r$ are assumed integrable for every positive $r$; this is explicit in Lean, where a Bochner integral of a non-integrable function would be $0$.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, pp. 22–23, Lemma 9, (32)–(35)

import Mathlib

namespace RandomLeadGBS.Diffusion
open Filter Topology MeasureTheory

theorem lemma_9 (μ ν : ℝ → Measure ℝ) (μA : Measure ℝ)
    (hμ : ∀ r, 0 < r → IsProbabilityMeasure (μ r))
    (hν : ∀ r, 0 < r → IsProbabilityMeasure (ν r))
    (hμA : IsProbabilityMeasure μA)
    (h32 : ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun r => ∫ x, g x ∂(μ r)) atTop (𝓝 (∫ x, g x ∂μA)))
    (hA : Integrable (fun x : ℝ => x) μA)
    (h33p : Tendsto (fun r => ∫ x, max x 0 ∂(μ r)) atTop (𝓝 (∫ x, max x 0 ∂μA)))
    (h33m : Tendsto (fun r => ∫ x, max (-x) 0 ∂(μ r)) atTop (𝓝 (∫ x, max (-x) 0 ∂μA)))
    (hst : ∀ r, 0 < r → ∀ x : ℝ, μ r (Set.Ioi x) ≤ ν r (Set.Ioi x))
    (hint : ∀ r, 0 < r →
      Integrable (fun x : ℝ => x) (μ r) ∧ Integrable (fun x : ℝ => x) (ν r))
    (hmean : Tendsto (fun r => ∫ x, x ∂(ν r) - ∫ x, x ∂(μ r)) atTop (𝓝 0)) :
    (∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun r => ∫ x, g x ∂(ν r)) atTop (𝓝 (∫ x, g x ∂μA))) ∧
    Tendsto (fun r => ∫ x, max x 0 ∂(ν r)) atTop (𝓝 (∫ x, max x 0 ∂μA)) ∧
    Tendsto (fun r => ∫ x, max (-x) 0 ∂(ν r)) atTop (𝓝 (∫ x, max (-x) 0 ∂μA)) := by sorry

end RandomLeadGBS.Diffusion
