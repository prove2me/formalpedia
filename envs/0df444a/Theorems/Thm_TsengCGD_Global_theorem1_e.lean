-- Prove2me | Theorems.Thm_TsengCGD_Global_theorem1_e
-- name    : TsengCGD.Global.theorem1_e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:14.467018+00:00
-- url     : https://prove2.me/theorems/ff11ea3e-e1cb-4bdd-829d-ae24abd4b86a
-- title:
--   Theorem 1(e) — every cluster point is stationary under generalized Gauss–Seidel selection
-- statement:
--   Consider a CGD run for $F_c=f+cP$ under Assumption 1. The steps use the Armijo rule with $\inf_k\alpha^k_{\mathrm{init}}>0$. Suppose every $T$ consecutive coordinate sets cover all coordinates, $P$ is block-separable with respect to each chosen set $\mathcal J^k$, and $\sup_k\alpha^k<\infty$. Then
--
--   $$\bar x\text{ a cluster point of }\{x^k\}
--   \quad\Longrightarrow\quad F_c'(\bar x;v)\ge0\quad\text{for every }v\in\mathbb R^n.$$
--
--   Thus every accumulation point satisfies the full directional first-order condition, despite the changing coordinate blocks and nonsmooth penalty.
--
--   **Formalization Note** The standing assumptions of (1), exact subproblem minimizers, first accepted Armijo trial, and the ranges of all line-search parameters are explicit. `MapClusterPt` encodes a cluster point without assuming the full run converges. Stationarity covers all directions, not only the current block. The upper bound on accepted steps is a finite real bound.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 399, Theorem 1(e), https://doi.org/10.1007/s10107-007-0170-0

import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem theorem1_e {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α αinit : ℕ → ℝ) (β σ γ lam lamBar : ℝ)
    (hrun : IsCGDRun f D P c J H x d α)
    (harm : IsArmijo f D P c β σ γ αinit H x d α)
    (hA1 : Assumption1 H lam lamBar)
    (hinit : ∃ a : ℝ, 0 < a ∧ ∀ k, a ≤ αinit k)
    (hGS : GaussSeidel J) (hsep : ∀ k, BlockSeparable D P (J k))
    (hsup : ∃ A : ℝ, ∀ k, α k ≤ A) :
    ∀ xbar : Vec n, MapClusterPt xbar atTop x → IsStationary f D P c xbar := by sorry

end TsengCGD.Global
