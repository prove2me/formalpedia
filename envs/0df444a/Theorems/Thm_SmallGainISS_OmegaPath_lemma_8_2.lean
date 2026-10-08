-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_lemma_8_2
-- name    : SmallGainISS.OmegaPath.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:15.091931+00:00
-- url     : https://prove2.me/theorems/745c3b42-3c86-4bc2-8ffa-269e1a2f0840
-- title:
--   Lemma 8.2 — $\Omega$ is invariant under $\Gamma_\mu$ and contains the segment from $s$ to $\Gamma_\mu(s)$
-- statement:
--   Throughout, $n\ge 0$ is the number of subsystems, $\mathbb R_+=[0,\infty)$, and vectors in $\mathbb R^n_+$ are compared componentwise: $v\le w$ means $v_i\le w_i$ for all $i$, and $v<w$ means $v_i<w_i$ for **all** $i$. $\Gamma=(\gamma_{ij})$ is a gain matrix with $\gamma_{ii}\equiv0$, $\mu=(\mu_1,\dots,\mu_n)$ is a vector of monotone aggregation functions on $\mathbb R^n_+$ compatible with $\Gamma$ in the sense of Remark 2.6, and $\Gamma_\mu(s)_i=\mu_i(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n))$ is the gain operator.
--
--   Assume all gains are in $\mathcal K\cup\{0\}$ and $\Gamma$ has no zero rows. If $s\in\Omega(\Gamma_\mu)$ is strictly positive ($s_i>0$ for all $i$), then
--
--   1. $\Gamma_\mu(s)$ is strictly positive and $\Gamma_\mu(s)\in\Omega(\Gamma_\mu)$;
--   2. for every $\lambda\in[0,1]$,
--   $$s_\lambda:=\lambda s+(1-\lambda)\Gamma_\mu(s)\in\Omega(\Gamma_\mu).$$
--
--   The small gain condition is not assumed. The lemma provides the line segments of the piecewise linear path of Lemma 8.3.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, pp. 21-22, Lemma 8.2

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Lemma 8.2 (pp. 21–22). If `Γ` has no zero rows and `0 < s ∈ Ω(Γ_μ)` (strictly positive),
then (i) `0 < Γ_μ(s) ∈ Ω` and (ii) `λ s + (1 - λ) Γ_μ(s) ∈ Ω` for all `λ ∈ [0, 1]`. -/
theorem lemma_8_2 {n : ℕ} (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0)
    (hΓ : ∀ i j, SmallGainISS.Lyapunov.IsKOrZero (Γ i j)) (hdiag : SmallGainISS.Lyapunov.ZeroDiagonal Γ) (hrows : NoZeroRows Γ)
    (hμ : ∀ i, SmallGainISS.Lyapunov.IsMAF (μ i)) (hcomp : Compatible Γ μ)
    (s : Fin n → ℝ≥0) (hpos : SPos s) (hs : s ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ)) :
    (SPos (gainOp Γ μ s) ∧ gainOp Γ μ s ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ)) ∧
    ∀ l : ℝ≥0, l ≤ 1 → l • s + (1 - l) • gainOp Γ μ s ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ) := by sorry

end SmallGainISS.OmegaPath
