-- Prove2me | Theorems.Thm_TsengBCD_Stationary_theorem_4_1_c
-- name    : TsengBCD.Stationary.theorem_4_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T22:19:42.121255+00:00
-- url     : https://prove2.me/theorems/c93a8fb0-3803-41d6-88ae-514255c4776c
-- title:
--   Theorem 4.1(c), p. 481 — at most one minimum in x₂, …, x_{N−1}, cyclic rule: cluster points of {x^r}_{r≡(N−1) mod N} are coordinatewise minima
-- statement:
--   Let $f:\mathbb R^{n_1+\cdots+n_N}\to\mathbb R\cup\{\infty\}$ never take the value $-\infty$, let $f(x^0)<\infty$, and assume that $X^0=\{x: f(x)\le f(x^0)\}$ is compact and that $f$ is continuous on $X^0$. Assume that $f(x_1,\dots,x_N)$ has at most one minimum in $x_k$ for $k=2,\dots,N-1$. Then for every sequence $\{x^r\}$ generated from $x^0$ by the BCD method using the cyclic rule and every cluster point $z$ of $\{x^r\}_{r\equiv(N-1)\bmod N}$:
--   1. $z$ is a coordinatewise minimum point of $f$;
--   2. if, in addition, $f$ is regular at $z$, then $z$ is a stationary point of $f$.
--
--   For $N=2$ there is no uniqueness hypothesis: cluster points of $x^1,x^3,x^5,\dots$ of two-block alternating minimization are coordinatewise minima.
--
--   **Formalization Note.** Blocks are 0-based: $\{2,\dots,N-1\}$ is the set of Lean indices $k$ with $1\le k<N-1$. "At most one minimum in $x_k$" counts only minimum points in the effective domain of the block section. The cyclic rule and the subsequence are as in Theorem 4.1(b). Continuity is continuity of $f$ at every point of $X^0$ (see Theorem 4.1(a)).
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), pp. 480–481, Theorem 4.1(c)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

namespace TsengBCD.Stationary

open Filter Topology

theorem theorem_4_1_c {N : ℕ} [NeZero N] {n : Fin N → ℕ} (f : X n → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (x0 : X n) (hx0 : f x0 ≠ ⊤) (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y) :
    ((∀ k : Fin N, 1 ≤ k.val → k.val < N - 1 → AtMostOneMinIn f k) →
      ∀ (s : ℕ → Fin N) (x : ℕ → X n), IsCyclic s → x 0 = x0 → IsBCDRun f s x →
        ∀ z, MapClusterPt z atTop (fun m : ℕ => x (N * m + (N - 1))) →
          IsCoordMin f z ∧ (IsRegularAt f z → IsStationary f z)) := by sorry

end TsengBCD.Stationary
