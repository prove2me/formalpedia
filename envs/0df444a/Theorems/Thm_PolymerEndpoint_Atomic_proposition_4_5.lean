-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_proposition_4_5
-- name    : PolymerEndpoint.Atomic.proposition_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:12.609981+00:00
-- url     : https://prove2.me/theorems/0615cae6-26fd-43cb-bfe9-25e7e06828ea
-- title:
--   Proposition 4.5 — $|F_n-\mathcal R(\mu_n)|\to0$ almost surely
-- statement:
--   Throughout, $d\geq1$; the disorder law $\mathfrak L$ is a non-degenerate probability measure on $\mathbb R$ with $\lambda(\alpha)=\log\mathbb E e^{\alpha X}<\infty$ for all $\alpha\in[-2\beta,2\beta]$ (the paper's (1.1)). Let $\beta>0$ and let $(X_u)$ be an i.i.d. environment with law $\mathfrak L$. Let $F_n=\frac1n\log Z_n$ be the quenched free energy, $\mu_n$ the empirical measure of the endpoint distributions $f_0,\dots,f_{n-1}$ (4.1), and $\mathcal R(\mu)=\int R(f)\,\mu(df)$ the lift (4.6) of the functional $R(f)=\mathbb E\log(\widetilde F/2d)$ of (3.8). Then
--
--   $$
--   \bigl|F_n-\mathcal R(\mu_n)\bigr|\longrightarrow0\qquad\text{almost surely as }n\to\infty.
--   $$
--
--   The free energy is thus asymptotically a continuous functional of the empirical endpoint law, which is how the variational formula of Theorem 4.7 arises.
--
--   **Formalization Note** The standing range is $\beta>0$ (§1.1).
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 34, Proposition 4.5 (with (4.6)–(4.7), p. 34)

import Definitions.Def_PolymerEndpoint_Atomic_Update

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

theorem proposition_4_5 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 < β) (hmom : MomentCondition 𝔏 β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Cell d → Ω → ℝ)
    (henv : IsEnvironment X 𝔏 P) :
    ∀ᵐ a ∂P, Tendsto
      (fun n : ℕ => |F X β n a - RR 𝔏 β (empirical X β n a)|)
      atTop (𝓝 0) := by sorry

end PolymerEndpoint.Atomic
