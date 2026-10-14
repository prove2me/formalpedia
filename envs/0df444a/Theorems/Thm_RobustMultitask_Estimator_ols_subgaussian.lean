-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_ols_subgaussian
-- name    : RobustMultitask.Estimator.ols_subgaussian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:43.467586+00:00
-- url     : https://prove2.me/theorems/741dbdbb-c5ed-48dc-9015-82e1ae2ab9e3
-- title:
--   Proof of Proposition 5, p. 41 — each OLS component β̂ʲ_ind,(i) is √(σⱼ²/(nⱼψ))-subgaussian with mean βʲ_(i)
-- statement:
--   Work in the fixed-design multitask model under Assumption 1 with constant $\psi>0$. For every task $j$ and component $i\in[d]$, the $i$-th component of the OLS estimator $\widehat\beta^j_{\mathrm{ind}}=(X^{j\top}X^j)^{-1}X^{j\top}Y^j$ is $\sqrt{\sigma_j^2/(n_j\psi)}$-subgaussian with mean $\beta^j_{(i)}$: for every $\lambda\in\mathbb R$,
--   $$\mathbb E\Big[\exp\big(\lambda(\widehat\beta^j_{\mathrm{ind},(i)}-\beta^j_{(i)})\big)\Big]\ \le\ \exp\Big(\frac{\lambda^2\sigma_j^2}{2n_j\psi}\Big).$$
--
--   This is what lets Proposition 4 be applied to the per-task OLS estimates: they are independent across tasks and subgaussian with task-dependent parameters.
--
--   **Formalization Note** Stated with Mathlib's `HasSubgaussianMGF`, whose second argument is the variance proxy, here $(\sqrt{\sigma_j^2/(n_j\psi)})^2=\sigma_j^2/(n_j\psi)$ in $\mathbb R_{\ge 0}$ (with $\psi$ coerced by `Real.toNNReal`, which is the identity since $\psi>0$). `HasSubgaussianMGF` also includes integrability of $\exp(t(\widehat\beta^j_{\mathrm{ind},(i)}-\beta^j_{(i)}))$ for every $t$.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 41, proof of Proposition 5 (unnumbered display)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_Model
import Definitions.Def_RobustMultitask_Estimator_Algorithm

namespace RobustMultitask.Estimator

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Proof of Proposition 5, p. 41 (unnumbered display). Under Assumption 1, each component
`β̂ʲ_ind,(i)` of the OLS estimator `β̂ʲ_ind = (XʲᵀXʲ)⁻¹XʲᵀYʲ` is `√(σ_j²/(n_jψ))`-subgaussian with
mean `βʲ_(i)`: `E[exp(λ(β̂ʲ_ind,(i) − βʲ_(i)))] ≤ exp(λ²σ_j²/(2n_jψ))` for every `λ ∈ ℝ`. The
variance proxy of `HasSubgaussianMGF` is the square `σ_j²/(n_jψ)`. -/
theorem ols_subgaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ)
    (hmodel : IsMultitaskModel P n X β βdag s σ ε) (ψ : ℝ) (hA1 : Assumption1 n X ψ)
    (j : Fin N) (i : Fin d) :
    HasSubgaussianMGF (fun ω => ols (X j) (response X β ε j ω) i - β j i)
      (σ j ^ 2 / ((n j : ℝ≥0) * Real.toNNReal ψ)) P := by sorry

end RobustMultitask.Estimator
