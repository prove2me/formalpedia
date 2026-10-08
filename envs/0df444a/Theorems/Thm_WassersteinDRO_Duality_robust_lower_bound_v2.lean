-- Prove2me | Theorems.Thm_WassersteinDRO_Duality_robust_lower_bound_v2
-- name    : WassersteinDRO.Duality.robust_lower_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:42.43585+00:00
-- url     : https://prove2.me/theorems/c43c8b38-fde7-4fd3-bd64-c3271ea33c4a
-- title:
--   Theorem 6 — robust lower bound on $R_{\varepsilon,p}(\hat P_N,\ell)$ by perturbed empirical distributions, on Borel $\mathbb{R}^m$
-- statement:
--   Let $E = \mathbb{R}^m$ with an arbitrary norm (a finite-dimensional real normed space) and its Borel $\sigma$-algebra, let $\Xi \subseteq E$ be closed, $p \in [1,\infty)$, $\varepsilon \ge 0$, and let $\hat P_N = \frac1N\sum_{i=1}^N \delta_{\hat\xi_i}$ be the empirical distribution of $N \ge 1$ training samples $\hat\xi_1,\dots,\hat\xi_N \in E$. For any measurable, upper semicontinuous, $\hat P_N$-integrable loss $\ell : E \to \mathbb{R}$ the worst-case risk is bounded below by the worst-case empirical loss over all perturbation matrices $\Theta = (\theta_1,\dots,\theta_N)$ in an $L_{p,1}$-norm uncertainty set:
--   $$R_{\varepsilon,p}(\hat P_N,\ell) \;\ge\; \sup\Big\{\frac1N\sum_{i=1}^N \ell(\hat\xi_i+\theta_i) \;:\; \theta_i \in E,\ \hat\xi_i+\theta_i \in \Xi\ \forall i,\ \frac1N\sum_{i=1}^N \|\theta_i\|^p \le \varepsilon^p\Big\}.$$
--   Both sides are taken in $[-\infty,\infty]$: the supremum is $+\infty$ for an unbounded constraint set and $-\infty$ if no perturbation is feasible (e.g. $\Xi = \emptyset$).
--
--   **Formalization Note.** The retired version was false because its $\sigma$-algebra on $E$ was a free parameter: with the trivial $\sigma$-algebra no non-constant loss is integrable under any probability measure, so the integrability-guarded worst-case risk was the supremum of the empty family, $-\infty$, while the left-hand side was a real number. The new statement does the following differently. (i) $E$ is a finite-dimensional real normed space (the paper's $\mathbb{R}^m$ with an arbitrary norm) carrying its Borel $\sigma$-algebra (`[FiniteDimensional ℝ E] [BorelSpace E]`); the retired version quantified over every `MeasurableSpace E`, including $\sigma$-algebras unrelated to the norm, for which the Wasserstein cost is a lower integral and non-constant losses are integrable under no measure. (ii) The worst-case risk is the paper's $\sup_{Q \in \mathcal{B}_{\varepsilon,p}} \mathbb{E}_Q[\ell]$ with the paper's p. 2 convention for non-integrable losses (`worstCaseRisk`/`nominalRisk` v2, valued in $[-\infty,\infty]$) instead of a supremum that silently discarded every $Q$ under which $\ell$ is not integrable. Standing assumptions made explicit: $\Xi$ closed (p. 6); $\hat P_N$ a probability distribution; $p \in [1,\infty)$ and $\varepsilon \ge 0$ (p. 3, 6); the loss is measurable (p. 1) and, by Assumption 1 (p. 9, "tacitly assumed to hold throughout the rest of the paper"), upper semicontinuous and $\hat P_N$-integrable. For a real-valued $\ell$ and the empirical $\hat P_N$ the integrability is automatic and is carried only for fidelity to Assumption 1; $N \ge 1$ matches the paper's indexing $i \in [N]$. Losses are taken real-valued, a special case of the paper's extended-real-valued losses that the retired version already made. No correction to the printed source.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), Theorem 6, p. 10, eq. (9) (setting p. 3, 6; Assumption 1, p. 9)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk_v2
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution

open MeasureTheory

namespace WassersteinDRO.Duality

/-- Theorem 6 (Robust lower bound), Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh,
*Wasserstein Distributionally Robust Optimization*, INFORMS TutORials 2019
(arXiv:1908.08729v2), p. 10, eq. (9): if `PN` is the empirical distribution of the training
samples `ξ̂₁,…,ξ̂_N`, then the worst-case risk (6) of any fixed loss function `ℓ ∈ L` is
bounded below by the worst-case empirical loss over all perturbation matrices
`Θ = (θ₁,…,θ_N)` in an `L_{p,1}`-norm uncertainty set:
`Rε,p(PN,ℓ) ≥ sup { (1/N) Σᵢ ℓ(ξ̂ᵢ+θᵢ) : θᵢ ∈ E, ξ̂ᵢ+θᵢ ∈ Ξ ∀i, (1/N) Σᵢ ‖θᵢ‖^p ≤ ε^p }`.

Setting (p. 3, 6, 9): `E` is `ℝ^m` with an arbitrary norm (finite-dimensional real normed
space) with its Borel σ-algebra; `Ξ ⊆ E` is closed; `p ∈ [1,∞)`, `ε ≥ 0`; `N ≥ 1` (the paper
indexes `i ∈ [N]`). The loss satisfies the standing conventions: measurable (p. 1) and, by
Assumption 1 (p. 9), upper semicontinuous and `PN`-integrable (automatic for a real-valued
`ℓ` and the empirical `PN`, but carried for fidelity). The finite supremum is taken in `EReal`
so that an unbounded constraint set gives `+∞` and an infeasible one (e.g. `Ξ = ∅`) gives
`-∞ = sup ∅`, exactly as in the paper.

Corrected from the retired `robust_lower_bound`: the σ-algebra was a free `[MeasurableSpace E]`
(with the trivial σ-algebra no non-constant `ℓ` was integrable under any `Q`, so the guarded
worst-case risk collapsed to `-∞`), `E` was not finite-dimensional, measurability/upper
semicontinuity of `ℓ` were missing, and the worst-case risk dropped non-integrable `Q` instead
of using the paper's convention (now `worstCaseRisk`/`nominalRisk` v2). -/
theorem robust_lower_bound_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞcl : IsClosed Ξ)
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) (hℓm : Measurable ℓ) (hℓusc : UpperSemicontinuous ℓ)
    (hℓ : Integrable ℓ (empiricalDistribution ξhat)) :
    (⨆ (θ : Fin N → E)
        (_ : ∀ i, ξhat i + θ i ∈ Ξ)
        (_ : (∑ i, ‖θ i‖ ^ p) / (N : ℝ) ≤ ε ^ p),
        (((∑ i, ℓ (ξhat i + θ i)) / (N : ℝ) : ℝ) : EReal))
      ≤ worstCaseRisk ε p Ξ (empiricalDistribution ξhat) ℓ := by sorry

end WassersteinDRO.Duality
