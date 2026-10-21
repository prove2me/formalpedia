-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_lemma_9
-- name    : RankOneBimatrix.BinSearch.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:11.104575+00:00
-- url     : https://prove2.me/theorems/0f8b32c9-f1d8-4826-93fc-46a467efab40
-- title:
--   Lemma 9, p. 10 — equilibria are optimal primal-dual pairs
-- statement:
--   For real $\lambda$, $(x,y)$ is an equilibrium of $(A,-A+\mathbf1\lambda b^\top)$ exactly when $y$ and $x$ extend to optimal solutions $(y,t)$ of $D_\lambda$ and $(x,v,s)$ of $P_\lambda$. The extensions are unique for the given strategies and parameter, with payoffs $-t$ and $v$.
--
--   $$-t=x^\top Ay,\qquad v=x^\top(-A+\mathbf1\lambda b^\top)y.$$
--
--   If $x^\top a=\lambda$, the pair is also an equilibrium of $(A,-A+ab^\top)$ with those payoffs. **Formalization Note** Both pure-strategy sets are nonempty.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 10, Lemma 9

import Definitions.Def_RankOneBimatrix_BinSearch_Setting

namespace RankOneBimatrix.BinSearch
open Matrix

/-- Lemma 9, p. 10: equilibrium iff primal-dual optimality, uniqueness,
and both players' payoff identities. -/
theorem lemma_9 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (lam : ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (IsNE A (-A + onesLam lam b) x y ↔
      ∃ (t v : ℝ) (s : Fin n → ℝ),
        (y, t) ∈ Yopt A b lam ∧ (x, v, s) ∈ POpt A b lam ∧
        (∀ t' : ℝ, (y, t') ∈ Yopt A b lam → t' = t) ∧
        (∀ (v' : ℝ) (s' : Fin n → ℝ),
          (x, v', s') ∈ POpt A b lam → v' = v ∧ s' = s) ∧
        -t = x ⬝ᵥ (A *ᵥ y) ∧
        v = x ⬝ᵥ ((-A + onesLam lam b) *ᵥ y)) ∧
    (∀ (t v : ℝ) (s : Fin n → ℝ),
      (y, t) ∈ Yopt A b lam → (x, v, s) ∈ POpt A b lam →
      x ⬝ᵥ a = lam →
      IsNE A (rankOneB A a b) x y ∧
        -t = x ⬝ᵥ (A *ᵥ y) ∧
        v = x ⬝ᵥ ((rankOneB A a b) *ᵥ y)) := by sorry

end RankOneBimatrix.BinSearch
