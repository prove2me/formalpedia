-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_lemma_8_1
-- name    : SmallGainISS.OmegaPath.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:27.178856+00:00
-- url     : https://prove2.me/theorems/02a79bd7-0bde-4156-b385-985dc05a796a
-- title:
--   Lemma 8.1 — under (SGC), the iterates $\Gamma_\mu^k(s)$ of a point of $\Omega$ tend to $0$
-- statement:
--   Throughout, $n\ge 0$ is the number of subsystems, $\mathbb R_+=[0,\infty)$, and vectors in $\mathbb R^n_+$ are compared componentwise: $v\le w$ means $v_i\le w_i$ for all $i$, and $v<w$ means $v_i<w_i$ for **all** $i$. $\Gamma=(\gamma_{ij})$ is a gain matrix with $\gamma_{ii}\equiv0$, $\mu=(\mu_1,\dots,\mu_n)$ is a vector of monotone aggregation functions on $\mathbb R^n_+$ compatible with $\Gamma$ in the sense of Remark 2.6, and $\Gamma_\mu(s)_i=\mu_i(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n))$ is the gain operator.
--
--   Assume all gains are in $\mathcal K\cup\{0\}$ and $\Gamma_\mu$ satisfies the small gain condition $\Gamma_\mu\not\ge\mathrm{id}$. If $s\in\Omega(\Gamma_\mu)$, i.e. $\Gamma_\mu(s)<s$, then
--   $$\lim_{k\to\infty}\Gamma_\mu^k(s)=0 .$$
--
--   This is the convergence fact behind the descent from a point of $\Omega$ to the origin in Lemma 8.3 and Proposition 8.4.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 21, Lemma 8.1

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Lemma 8.1 (p. 21). If `Γ_μ` satisfies (SGC) and `s ∈ Ω(Γ_μ)`, then `Γ_μᵏ(s) → 0`. -/
theorem lemma_8_1 {n : ℕ} (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0)
    (hΓ : ∀ i j, SmallGainISS.Lyapunov.IsKOrZero (Γ i j)) (hdiag : SmallGainISS.Lyapunov.ZeroDiagonal Γ) (hμ : ∀ i, SmallGainISS.Lyapunov.IsMAF (μ i))
    (hcomp : Compatible Γ μ) (hsgc : SGC (gainOp Γ μ))
    (s : Fin n → ℝ≥0) (hs : s ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ)) :
    Tendsto (fun k : ℕ => (gainOp Γ μ)^[k] s) atTop (𝓝 0) := by sorry

end SmallGainISS.OmegaPath
