-- Prove2me | Theorems.Thm_TsengBCD_Hemivariate_argmin_attained
-- name    : TsengBCD.Hemivariate.argmin_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:09.586709+00:00
-- url     : https://prove2.me/theorems/1a158574-b205-4c37-aea0-97de459a2d78
-- title:
--   §2, p. 478, remark after (3) — bounded level set and lsc f: X⁰ is compact and each block minimization (2) is attained
-- statement:
--   Let $f:\mathbb R^{n_1+\cdots+n_N}\to[-\infty,\infty]$ be lower semicontinuous and let $x^0$ be a point such that the level set
--   $$X^0=\{x: f(x)\le f(x^0)\}$$
--   is bounded. Then $X^0$ is compact, and for every $y\in X^0$ and every block $k\in\{1,\dots,N\}$ the block minimization
--   $$\min_{x_k} f(y_1,\dots,y_{k-1},x_k,y_{k+1},\dots,y_N)$$
--   is attained.
--
--   This is the remark that makes the BCD method well defined: every iterate stays in $X^0$, so step (2) always has a minimizer.
--
--   **Formalization Note.** The page's "$f$ is lsc on $X^0$" is read as lower semicontinuity of $f$ on the whole space, which Assumption B3 provides for $f=f_0+\sum_k f_k$. Lower semicontinuity of the restriction to $X^0$ alone would not make $X^0$ closed. The remark is general, so the statement is for an arbitrary $f$.
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), p. 478, §2, remark after (3)

import Mathlib
import Definitions.Def_TsengBCD_Hemivariate_Setting

namespace TsengBCD.Hemivariate

open Filter Topology

theorem argmin_attained {N : ℕ} {n : Fin N → ℕ} (f : TsengBCD.Stationary.X n → EReal) (x0 : TsengBCD.Stationary.X n)
    (hbdd : Bornology.IsBounded (TsengBCD.Stationary.levelSet f x0)) (hlsc : LowerSemicontinuous f) :
    IsCompact (TsengBCD.Stationary.levelSet f x0) ∧
      ∀ y ∈ TsengBCD.Stationary.levelSet f x0, ∀ k : Fin N, ∃ a : EuclideanSpace ℝ (Fin (n k)),
        ∀ b : EuclideanSpace ℝ (Fin (n k)),
          f (Function.update y k a) ≤ f (Function.update y k b) := by sorry

end TsengBCD.Hemivariate
