-- Prove2me | Theorems.Thm_ProbMFG_Existence_lemma_2_1
-- name    : ProbMFG.Existence.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:57.878535+00:00
-- url     : https://prove2.me/theorems/da0730bf-877e-4cbc-82b1-f84f20c565e5
-- title:
--   Lemma 2.1 — unique Hamiltonian minimizer and regularity
-- statement:
--   Assume (A.1)–(A.2), with positive strong-convexity constant $\lambda$ and gradient regularity constant $c_L$. Suppose $\|b_2(t)\|\le B_2$ on $[0,T]$. For every $t\in[0,T]$, $x,y\in\mathbb R^d$ and $\mu\in\mathcal P_2(\mathbb R^d)$, the Hamiltonian has a unique minimizer $\hat a(t,x,\mu,y)$. It is measurable, locally bounded and uniformly Lipschitz in $(x,y)$, with a Lipschitz constant depending only on $\lambda,c_L,B_2$. Moreover,
--   $$\|\hat a(t,x,\mu,y)\|\le\lambda^{-1}\bigl(\|\partial_a f(t,x,\mu,0)\|+\|b_2(t)\|\,\|y\|\bigr).$$
--   This minimizer makes the forward equation in (2.13) a defined feedback system.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2709, Lemma 2.1 and (2.9); https://doi.org/10.1137/120883499

import Mathlib
import Definitions.Def_ProbMFG_Existence_Model

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMFG.Existence

/-- Lemma 2.1 and its displayed bound (2.9). The Lipschitz constant is uniform
in the model given λ, c_L, and the bound on b₂. -/
theorem lemma_2_1 (lam cL B₂ : ℝ) (hlam : 0 < lam) (hcL : 0 < cL) (hB₂ : 0 ≤ B₂) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {d m k : ℕ} (M : Model d m k),
      M.A1 → M.A2 lam cL → (∀ t ≤ M.T, ‖M.b₂ t‖ ≤ B₂) →
      (∀ t ≤ M.T, ∀ μ, IsP2 μ → ∀ x y : State d,
        (∀ a : Action k, M.H t x μ y (M.alphaHat t x μ y) ≤ M.H t x μ y a) ∧
        (∀ a : Action k, (∀ a', M.H t x μ y a ≤ M.H t x μ y a') →
          a = M.alphaHat t x μ y) ∧
        ‖M.alphaHat t x μ y‖ ≤
          lam⁻¹ * (‖M.dfa t x μ 0‖ + ‖M.b₂ t‖ * ‖y‖)) ∧
      (∀ t ≤ M.T, ∀ μ, IsP2 μ → ∀ x x' y y' : State d,
        ‖M.alphaHat t x μ y - M.alphaHat t x' μ y'‖ ≤
          L * (‖x - x'‖ + ‖y - y'‖)) ∧
      Measurable (fun q : {t : ℝ≥0 // t ≤ M.T} × State d ×
          {μ : Measure (State d) // IsP2 μ} × State d =>
        M.alphaHat q.1.1 q.2.1 q.2.2.1.1 q.2.2.2) ∧
      (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
        ∀ t ≤ M.T, ∀ μ, IsP2 μ → (moment 2 μ).toReal ≤ R →
          ∀ x y : State d, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖M.alphaHat t x μ y‖ ≤ C) := by sorry

end ProbMFG.Existence
