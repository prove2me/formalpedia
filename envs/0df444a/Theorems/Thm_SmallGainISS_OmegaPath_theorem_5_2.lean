-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_theorem_5_2
-- name    : SmallGainISS.OmegaPath.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:12.897744+00:00
-- url     : https://prove2.me/theorems/8f0e4239-f14a-44fe-9d70-d9108c135e1f
-- title:
--   Theorem 5.2 — under the small gain condition (in four settings) an $\Omega$-path exists
-- statement:
--   Let $\Gamma=(\gamma_{ij})$ be a gain matrix with $\gamma_{ii}\equiv0$ and $\mu=(\mu_1,\dots,\mu_n)$ a vector of monotone aggregation functions on $\mathbb R^n_+$, compatible with $\Gamma$ (Remark 2.6). Let $\Gamma_\mu(s)_i=\mu_i(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n))$. Assume one of the following:
--
--   1. all $\gamma_{ij}\in\mathcal K_\infty\cup\{0\}$, $\Gamma_\mu$ is linear (given by a real matrix with nonnegative entries) and its spectral radius is less than one;
--   2. all $\gamma_{ij}\in\mathcal K_\infty\cup\{0\}$, $\Gamma$ is irreducible and $\Gamma_\mu\not\ge\mathrm{id}$;
--   3. all $\gamma_{ij}\in\mathcal K_\infty\cup\{0\}$, $\mu=\max$ and $\Gamma_\mu\not\ge\mathrm{id}$;
--   4. all $\gamma_{ij}\in(\mathcal K\setminus\mathcal K_\infty)\cup\{0\}$ (so $\Gamma_\mu$ is bounded) and $\Gamma_\mu\not\ge\mathrm{id}$.
--
--   Then there exists an $\Omega$-path $\sigma$ with respect to $\Gamma_\mu$: each $\sigma_i\in\mathcal K_\infty$, each $\sigma_i^{-1}$ is locally Lipschitz on $(0,\infty)$ with derivative bounds $0<c\le(\sigma_i^{-1})'\le C$ on compact subsets of $(0,\infty)$, and
--   $$\Gamma_\mu(\sigma(r))<\sigma(r)\qquad\text{for all } r>0 .$$
--
--   Here $\Gamma_\mu\not\ge\mathrm{id}$ means that $s\le\Gamma_\mu(s)$ fails for every $s\ne0$, and $<$ is strict in every component. The theorem is the first of the paper's two main results; an $\Omega$-path is exactly what the second (Theorem 5.3) needs to assemble an ISS Lyapunov function for the network.
--
--   **Formalization Note** The theorem's header types $\Gamma\in(\mathcal K_\infty\cup\{0\})^{n\times n}$, while case (iv) requires bounded entries; the two are compatible only for $\Gamma=0$. Each case therefore carries its own entry class, as the proof in §8.5 uses it. Case (iv) is stated as printed, without the no-zero-rows hypothesis of Proposition 8.4. The four cases are one hypothesis given as a disjunction.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 13, Theorem 5.2 (proof: §8.5, p. 27)

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator
import Definitions.Def_SmallGainISS_OmegaPath_IsOmegaPath

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Theorem 5.2 (p. 13). Let `Γ` be a gain matrix with `γᵢᵢ ≡ 0`, `μ ∈ MAFⁿₙ`, compatible with `Γ`
(Remark 2.6). Assume one of
(i) `Γ ∈ (𝒦∞ ∪ {0})ⁿˣⁿ`, `Γ_μ` is linear and its spectral radius is less than one;
(ii) `Γ ∈ (𝒦∞ ∪ {0})ⁿˣⁿ`, `Γ` is irreducible and `Γ_μ ≱ id`;
(iii) `Γ ∈ (𝒦∞ ∪ {0})ⁿˣⁿ`, `μ = max` and `Γ_μ ≱ id`;
(iv) `Γ ∈ ((𝒦 \ 𝒦∞) ∪ {0})ⁿˣⁿ` (so `Γ_μ` is bounded) and `Γ_μ ≱ id`.
Then there exists an Ω-path `σ` with respect to `Γ_μ`. -/
theorem theorem_5_2 {n : ℕ} (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0)
    (hdiag : SmallGainISS.Lyapunov.ZeroDiagonal Γ) (hμ : ∀ i, SmallGainISS.Lyapunov.IsMAF (μ i)) (hcomp : Compatible Γ μ)
    (hcases :
      ((∀ i j, SmallGainISS.Lyapunov.IsKInfOrZero (Γ i j)) ∧ IsLinearSpectralRadiusLtOne (gainOp Γ μ)) ∨
      ((∀ i j, SmallGainISS.Lyapunov.IsKInfOrZero (Γ i j)) ∧ IsIrreducible Γ ∧ SGC (gainOp Γ μ)) ∨
      ((∀ i j, SmallGainISS.Lyapunov.IsKInfOrZero (Γ i j)) ∧ μ = maxAgg ∧ SGC (gainOp Γ μ)) ∨
      ((∀ i j, IsBoundedKOrZero (Γ i j)) ∧ SGC (gainOp Γ μ))) :
    ∃ σ : ℝ≥0 → Fin n → ℝ≥0, IsOmegaPath (gainOp Γ μ) σ := by sorry

end SmallGainISS.OmegaPath
