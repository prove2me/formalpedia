-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_theorem_8_11
-- name    : SmallGainISS.OmegaPath.theorem_8_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:32.384986+00:00
-- url     : https://prove2.me/theorems/241dd075-9bbd-4904-9e8e-bd105d3b9d7e
-- title:
--   Theorem 8.11 — for irreducible $\Gamma\in(\mathcal K_\infty\cup\{0\})^{n\times n}$ with $\Gamma_\mu\not\ge\mathrm{id}$, a strictly increasing $\mathcal K_\infty$ path in $\Omega$
-- statement:
--   Throughout, $n\ge 0$ is the number of subsystems, $\mathbb R_+=[0,\infty)$, and vectors in $\mathbb R^n_+$ are compared componentwise: $v\le w$ means $v_i\le w_i$ for all $i$, and $v<w$ means $v_i<w_i$ for **all** $i$. $\Gamma=(\gamma_{ij})$ is a gain matrix with $\gamma_{ii}\equiv0$, $\mu=(\mu_1,\dots,\mu_n)$ is a vector of monotone aggregation functions on $\mathbb R^n_+$ compatible with $\Gamma$ in the sense of Remark 2.6, and $\Gamma_\mu(s)_i=\mu_i(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n))$ is the gain operator.
--
--   Assume all gains are in $\mathcal K_\infty\cup\{0\}$, $\Gamma$ is irreducible and $\Gamma_\mu\not\ge\mathrm{id}$. Then there exists a strictly increasing continuous path $\sigma:\mathbb R_+\to\mathbb R^n_+$ with every component $\sigma_i\in\mathcal K_\infty$ and
--   $$\Gamma_\mu(\sigma(r))<\sigma(r)\qquad\text{for all } r>0 .$$
--
--   This is case (ii) of Theorem 5.2 up to the regularity conditions (i)–(ii) of Definition 5.1, which the paper's piecewise linear construction also provides.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 24, Theorem 8.11

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Theorem 8.11 (p. 24). For `Γ ∈ (𝒦∞ ∪ {0})ⁿˣⁿ` irreducible, `μ ∈ MAFⁿₙ` and `Γ_μ ≱ id`, there is a
strictly increasing continuous path `σ` with every component `σᵢ ∈ 𝒦∞` and
`Γ_μ(σ(r)) < σ(r)` for all `r > 0` (strict componentwise). -/
theorem theorem_8_11 {n : ℕ} (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0)
    (hΓ : ∀ i j, SmallGainISS.Lyapunov.IsKInfOrZero (Γ i j)) (hdiag : SmallGainISS.Lyapunov.ZeroDiagonal Γ) (hμ : ∀ i, SmallGainISS.Lyapunov.IsMAF (μ i))
    (hcomp : Compatible Γ μ) (hirr : IsIrreducible Γ) (hsgc : SGC (gainOp Γ μ)) :
    ∃ σ : ℝ≥0 → Fin n → ℝ≥0, Continuous σ ∧ (∀ i, SmallGainISS.Lyapunov.IsKInf fun r => σ r i) ∧
      ∀ r : ℝ≥0, 0 < r → SmallGainISS.Lyapunov.SLt (gainOp Γ μ (σ r)) (σ r) := by sorry

end SmallGainISS.OmegaPath
