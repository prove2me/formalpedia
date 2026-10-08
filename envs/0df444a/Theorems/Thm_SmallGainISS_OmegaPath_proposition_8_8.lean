-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_proposition_8_8
-- name    : SmallGainISS.OmegaPath.proposition_8_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:31.455252+00:00
-- url     : https://prove2.me/theorems/18d4d591-1292-47a5-bba8-ef2a6a7d1a72
-- title:
--   Proposition 8.8 — $\Psi$ is path-connected; strictly increasing paths from $0$ to points of $\Omega$
-- statement:
--   Throughout, $n\ge 0$ is the number of subsystems, $\mathbb R_+=[0,\infty)$, and vectors in $\mathbb R^n_+$ are compared componentwise: $v\le w$ means $v_i\le w_i$ for all $i$, and $v<w$ means $v_i<w_i$ for **all** $i$. $\Gamma=(\gamma_{ij})$ is a gain matrix with $\gamma_{ii}\equiv0$, $\mu=(\mu_1,\dots,\mu_n)$ is a vector of monotone aggregation functions on $\mathbb R^n_+$ compatible with $\Gamma$ in the sense of Remark 2.6, and $\Gamma_\mu(s)_i=\mu_i(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n))$ is the gain operator.
--
--   Assume all gains are in $\mathcal K\cup\{0\}$ and $\Gamma_\mu$ satisfies the small gain condition. Then the decay set $\Psi(\Gamma_\mu)=\{s:\Gamma_\mu(s)\le s\}$ is nonempty and path-connected. If moreover $\Gamma_\mu(v)<\Gamma_\mu(w)$ whenever $v<w$, then for every $s\in\Omega(\Gamma_\mu)$ there is a continuous path $p:[0,1]\to\mathbb R^n_+$ with
--   $$p(0)=0,\quad p(1)=s,\quad t\mapsto p_i(t)\ \text{strictly increasing for every } i,\quad p(t)\in\Omega(\Gamma_\mu)\ \ (0<t\le1).$$
--
--   The paper calls such a $p$ a strictly increasing $\Omega$-path connecting $0$ and $s$; it is a finite path, not a path in the sense of Definition 5.1.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 23, Proposition 8.8

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Proposition 8.8 (p. 23). If `Γ_μ` satisfies (SGC), the decay set `Ψ(Γ_μ)` is nonempty and
path-connected. If moreover `Γ_μ(v) < Γ_μ(w)` whenever `v < w`, then for every `s ∈ Ω(Γ_μ)` there
is a path `p : [0, 1] → ℝⁿ₊` from `0` to `s`, every component strictly increasing, with
`p(t) ∈ Ω(Γ_μ)` for `t > 0` (a strictly increasing Ω-path connecting `0` and `s`). -/
theorem proposition_8_8 {n : ℕ} (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0)
    (hΓ : ∀ i j, SmallGainISS.Lyapunov.IsKOrZero (Γ i j)) (hdiag : SmallGainISS.Lyapunov.ZeroDiagonal Γ) (hμ : ∀ i, SmallGainISS.Lyapunov.IsMAF (μ i))
    (hcomp : Compatible Γ μ) (hsgc : SGC (gainOp Γ μ)) :
    (Psi (gainOp Γ μ)).Nonempty ∧ IsPathConnected (Psi (gainOp Γ μ)) ∧
    (StrictlyIncreasingOp (gainOp Γ μ) →
      ∀ s ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ), ∃ p : Path (0 : Fin n → ℝ≥0) s,
        (∀ i, StrictMono fun t : unitInterval => p t i) ∧
        ∀ t : unitInterval, 0 < t → p t ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ)) := by sorry

end SmallGainISS.OmegaPath
