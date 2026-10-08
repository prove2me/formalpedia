-- Prove2me | Theorems.Thm_TsengBCD_Stationary_argmin_attained
-- name    : TsengBCD.Stationary.argmin_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T22:18:02.072333+00:00
-- url     : https://prove2.me/theorems/3cf6e017-dba2-4741-a681-eb48ed4caa11
-- title:
--   Proof of Theorem 4.1, p. 481 — on a compact level set where f is continuous, each block minimization (2) is attained
-- statement:
--   Let $f:\mathbb R^{n_1+\cdots+n_N}\to\mathbb R\cup\{\infty\}$ never take the value $-\infty$, let $f(x^0)<\infty$, assume $X^0=\{x: f(x)\le f(x^0)\}$ is compact and $f$ is continuous at every point of $X^0$. Then for every $y\in X^0$ and every block $k$ there is $a\in\mathbb R^{n_k}$ with
--   $$f(y_1,\dots,y_{k-1},a,y_{k+1},\dots,y_N)\le f(y_1,\dots,y_{k-1},b,y_{k+1},\dots,y_N)\qquad\text{for all } b\in\mathbb R^{n_k}.$$
--
--   This is the statement "$x^{r+1}$ is defined" in the induction of the proof of Theorem 4.1: whichever block is chosen, the minimization (2) has a solution, so the BCD method can always proceed.
--
--   **Formalization Note.** "f is continuous on $X^0$" is formalized as continuity of $f$, as a map into $\mathbb R\cup\{\infty\}$, at every point of $X^0$ (see the goal theorem for why); for this step continuity of the restriction to $X^0$ would already suffice.
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), p. 481, proof of Theorem 4.1, first sentence ("x^{r+1} is defined")

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

namespace TsengBCD.Stationary

open Filter Topology

theorem argmin_attained {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (x0 : X n) (hx0 : f x0 ≠ ⊤) (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y) :
    ∀ y ∈ levelSet f x0, ∀ k : Fin N, ∃ a : EuclideanSpace ℝ (Fin (n k)),
      ∀ b : EuclideanSpace ℝ (Fin (n k)),
        f (Function.update y k a) ≤ f (Function.update y k b) := by sorry

end TsengBCD.Stationary
