-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_lemma_2_2
-- name    : RelaxedEqMDP.Discrete.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:43.921988+00:00
-- url     : https://prove2.me/theorems/1858d2f0-b89b-4420-b9d7-81e79b16badb
-- title:
--   Lemma 2.2, p. 8 — fixed points $y^n=\Psi_{\lambda_n}(y^n)$ are bounded as $\lambda_n\downarrow0$
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumptions 2.1, 2.2 and 2.3 hold. Let $(\lambda_n)_{n\in\mathbb N}\subset(0,1]$ decrease to $0$, and let $y^n\in\mathbb R^d$ satisfy $y^n=\Psi_{\lambda_n}(y^n)$ for every $n$. Then
--   $$\sup_{n\in\mathbb N}|y^n|<\infty.$$
--
--   Boundedness gives a convergent subsequence of the regularized equilibrium values, the starting point of the proof of Theorem 2.2.
--
--   **Formalization Note** $\lambda_n\downarrow0$ is: $0<\lambda_n\le1$, $(\lambda_n)$ nonincreasing, $\lambda_n\to0$. The conclusion is a uniform bound $C$ on the Euclidean norms $|y^n|$.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 8, Lemma 2.2

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Lemma 2.2, p. 8: under Assumptions 2.1–2.3, if `λ_n ∈ (0,1]`, `λ_n ↓ 0` and
`yⁿ = Ψ_{λ_n}(yⁿ)` for every `n`, then `sup_n |yⁿ| < ∞`. -/
theorem lemma_2_2 {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ)
    (Theta iota vartheta : ℝ) (hS : Standing U p) (h21 : Assumption21 U f δ)
    (h22 : Assumption22 U f p Theta) (h23 : Assumption23 U iota vartheta)
    (lam : ℕ → ℝ) (hlam : IsLamSeq lam) (y : ℕ → Fin d → ℝ)
    (hy : ∀ n, y n = PsiLam U p f δ (lam n) (y n)) :
    ∃ C : ℝ, ∀ n, enorm2 (y n) ≤ C := by sorry
end RelaxedEqMDP.Discrete
