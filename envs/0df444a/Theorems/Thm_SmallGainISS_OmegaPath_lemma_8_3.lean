-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_lemma_8_3
-- name    : SmallGainISS.OmegaPath.lemma_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:14.801056+00:00
-- url     : https://prove2.me/theorems/54e53abf-cd08-461e-a9a3-a5aab51776ed
-- title:
--   Lemma 8.3 — a path in $\Omega\cup\{0\}$ connects the origin with any $s\in\Omega$
-- statement:
--   Throughout, $n\ge 0$ is the number of subsystems, $\mathbb R_+=[0,\infty)$, and vectors in $\mathbb R^n_+$ are compared componentwise: $v\le w$ means $v_i\le w_i$ for all $i$, and $v<w$ means $v_i<w_i$ for **all** $i$. $\Gamma=(\gamma_{ij})$ is a gain matrix with $\gamma_{ii}\equiv0$, $\mu=(\mu_1,\dots,\mu_n)$ is a vector of monotone aggregation functions on $\mathbb R^n_+$ compatible with $\Gamma$ in the sense of Remark 2.6, and $\Gamma_\mu(s)_i=\mu_i(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n))$ is the gain operator.
--
--   Assume all gains are in $\mathcal K\cup\{0\}$, $\Gamma$ has no zero rows and $\Gamma_\mu$ satisfies the small gain condition. Let $s\in\Omega(\Gamma_\mu)$. Then there is a continuous path $p:[0,1]\to\mathbb R^n_+$ with
--   $$p(0)=0,\qquad p(1)=s,\qquad p(t)\in\Omega(\Gamma_\mu)\ \text{ for all } t\in(0,1],$$
--   so that $p$ runs in $\Omega\cup\{0\}$.
--
--   This is the "finite part" of every $\Omega$-path built in §8: it joins the origin to a chosen point of $\Omega$.
--
--   **Formalization Note** The path is a Mathlib `Path 0 s` on the unit interval. The conclusion "$p(t)\in\Omega$ for $t>0$" is the reading of "a path in $\Omega\cup\{0\}$ connecting the origin and $s$" that the paper's construction delivers and later uses.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 22, Lemma 8.3

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Lemma 8.3 (p. 22). If `Γ` has no zero rows, `Γ_μ` satisfies (SGC) and `s ∈ Ω(Γ_μ)`, there is a
path from the origin to `s` lying in `Ω ∪ {0}`; it leaves `0` immediately: `p(t) ∈ Ω` for `t > 0`. -/
theorem lemma_8_3 {n : ℕ} (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0)
    (hΓ : ∀ i j, SmallGainISS.Lyapunov.IsKOrZero (Γ i j)) (hdiag : SmallGainISS.Lyapunov.ZeroDiagonal Γ) (hrows : NoZeroRows Γ)
    (hμ : ∀ i, SmallGainISS.Lyapunov.IsMAF (μ i)) (hcomp : Compatible Γ μ) (hsgc : SGC (gainOp Γ μ))
    (s : Fin n → ℝ≥0) (hs : s ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ)) :
    ∃ p : Path (0 : Fin n → ℝ≥0) s,
      ∀ t : unitInterval, 0 < t → p t ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ) := by sorry

end SmallGainISS.OmegaPath
