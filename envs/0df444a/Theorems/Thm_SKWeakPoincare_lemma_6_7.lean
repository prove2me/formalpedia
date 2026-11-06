-- Prove2me | Theorems.Thm_SKWeakPoincare_lemma_6_7
-- name    : SKWeakPoincare.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:13.246294+00:00
-- url     : https://prove2.me/theorems/0b0663ef-3f79-4e22-a661-8794ba9b9520
-- title:
--   Lemma 6.7 — simulated annealing from weak Poincaré inequalities (corrected: $\delta_j\ge0$)
-- statement:
--   Let $\mu_0,\dots,\mu_L$ be probability measures on the same finite space. For $1\le j\le L$ let $P_j$ be reversible with stationary law $\mu_j$ and nonnegative spectrum, and suppose
--   $$
--   \mu_{j-1}\le B_j\mu_j,\qquad\mathrm{Var}_{\mu_j}[f]\le A_j\langle f,(I-P_j)f\rangle_{\mu_j}+\delta_j\operatorname{osc}(f)^2\ \ \text{for all }f,\qquad A_j\ge1,\qquad\delta_j\ge0.
--   $$
--   Then for nonnegative integers $k_1,\dots,k_L$,
--   $$
--   d_{\mathrm{TV}}\big(\mu_0P_1^{k_1}\cdots P_L^{k_L},\mu_L\big)\le\frac12\sum_{j=1}^L\Big(e^{-k_j/A_j}(B_j-1)+\delta_jB_j^2\Big)^{1/2}.
--   $$
--
--   This is a discrete-time, finite-state version of [HMRW25, Theorem 4.13]. Applied to the Gibbs laws $\mu_{\beta_j,A}$ along the schedule of Algorithm 1, it gives the sampling guarantee of Theorem 1.2.
--
--   **Formalization Note** $P_j$ is a stochastic matrix; nonnegative spectrum is $\langle f,P_jf\rangle_{\mu_j}\ge0$; $\mu_0P_1^{k_1}\cdots P_L^{k_L}$ is `chainRun (μ 0) P k L`.
--
--   Differences from the source:
--   - correction: no sign condition on δ_j → 0 ≤ δ_j for 1 ≤ j ≤ L; reason: the printed statement is false for δ_j < 0: with L = 1 and μ₀, μ₁, P₁, A₁, B₁, δ₁, k₁ as in the counterexample to Lemma 6.6 (on {true, false} with μ uniform, P(x,y) = 1/2, A₀ = 2, δ = −1/4, μinit the point mass at true (2-warm) and k = 0, every hypothesis holds (Var_μ[f] = (f(true) − f(false))²/4 = 2𝓔 − ¼osc²) but d_TV(μinit, μ) = 1/2 > 0 = ½(e⁰(2 − 1) − ¼·4)^{1/2}; proved in Solutions/verification/SKWeakPoincare_sanity.lean)
--   - encoding: P_j reversible with stationary law μ_j → IsStochastic (P j) and IsReversible (μ j) (P j); reason: P_j is a Markov kernel; detailed balance makes μ_j stationary
--   - encoding: nonnegative spectrum → HasNonnegSpectrum (μ j) (P j); reason: for a reversible P_j, P_j is self-adjoint in L²(μ_j), and its spectrum is nonnegative iff the quadratic form is
--   - encoding: μ_{j−1} ≤ B_jμ_j → IsWarm (μ (j−1)) (μ j) (B j), pointwise; reason: inequality of measures on a finite space
--   - encoding: μ₀, …, μ_L, P_j, A_j, B_j, δ_j, k_j → sequences indexed by ℕ, used only at indices ≤ L; reason: only those indices enter
--   - encoding: a finite space → a Fintype α with [Nonempty α]; reason: a finite space carrying a probability law is nonempty, and osc needs a nonempty space
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Lemma 6.7, p.43 ([HMRW25, Theorem 4.13])

import Mathlib
import Definitions.Def_SKWeakPoincare_fMean

namespace SKWeakPoincare

/-- **Lemma 6.7 (simulated annealing, [HMRW25, Theorem 4.13]) (corrected: `δ_j ≥ 0`).**
Hou–Liu–Yu, arXiv:2610.09882, Lemma 6.7, p. 43.

Let `μ₀, …, μ_L` be probability measures on the same finite space. For `1 ≤ j ≤ L` let `P_j` be
reversible with stationary law `μ_j` and nonnegative spectrum, and suppose `μ_{j−1} ≤ B_j μ_j`,
`Var_{μ_j}[f] ≤ A_j ⟨f, (I − P_j)f⟩_{μ_j} + δ_j osc(f)²` for every `f`, `A_j ≥ 1` and `δ_j ≥ 0`. Then,
for nonnegative integers `k₁, …, k_L`,
`d_TV(μ₀ P₁^{k₁} ⋯ P_L^{k_L}, μ_L) ≤ ½ Σ_{j=1}^{L} (e^{−k_j/A_j}(B_j − 1) + δ_j B_j²)^{1/2}`.

**Formalization Note.** `P_j` is a stochastic matrix (`IsStochastic`; "reversible with stationary law"
refers to a Markov kernel), reversible for `μ_j`; nonnegative spectrum is `HasNonnegSpectrum`;
`μ_{j−1} ≤ B_j μ_j` is `IsWarm (μ (j-1)) (μ j) (B j)`; `chainRun (μ 0) P k L` is
`μ₀ P₁^{k₁} ⋯ P_L^{k_L}`. The hypothesis `δ_j ≥ 0` is added: the printed statement is false for
`δ_j < 0` (see the item's differences list). Only indices `j ≤ L` of the sequences are used. -/
theorem lemma_6_7 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (L : ℕ) (μ : ℕ → α → ℝ) (P : ℕ → Matrix α α ℝ) (A B δ : ℕ → ℝ) (k : ℕ → ℕ)
    (hμ : ∀ j ≤ L, IsLaw (μ j))
    (hP : ∀ j ∈ Finset.Icc 1 L,
      IsStochastic (P j) ∧ IsReversible (μ j) (P j) ∧ HasNonnegSpectrum (μ j) (P j) ∧
        IsWarm (μ (j - 1)) (μ j) (B j) ∧ 1 ≤ A j ∧ 0 ≤ δ j ∧
        ∀ f : α → ℝ, fVar (μ j) f ≤ A j * fDirichlet (μ j) (P j) f + δ j * fOsc f ^ 2) :
    fTV (chainRun (μ 0) P k L) (μ L) ≤
      (1 / 2) * ∑ j ∈ Finset.Icc 1 L,
        Real.sqrt (Real.exp (-((k j : ℝ) / A j)) * (B j - 1) + δ j * B j ^ 2) := by sorry

end SKWeakPoincare
