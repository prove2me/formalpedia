-- Prove2me | Theorems.Thm_TsengBCD_Stationary_theorem_4_1_a
-- name    : TsengBCD.Stationary.theorem_4_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T22:18:51.13399+00:00
-- url     : https://prove2.me/theorems/4e45023c-ebb8-42c7-9d9c-a22e241fdcd7
-- title:
--   Theorem 4.1(a), p. 481 — pseudoconvex in every pair of blocks and regular on X⁰: every cluster point of essentially cyclic BCD is stationary
-- statement:
--   Let $f:\mathbb R^{n_1+\cdots+n_N}\to\mathbb R\cup\{\infty\}$ never take the value $-\infty$, let $f(x^0)<\infty$, and assume that the level set $X^0=\{x: f(x)\le f(x^0)\}$ is compact and that $f$ is continuous on $X^0$. Assume further that
--   1. $f(x_1,\dots,x_N)$ is pseudoconvex in $(x_k,x_i)$ for every $i,k\in\{1,\dots,N\}$, and
--   2. $f$ is regular at every $x\in X^0$.
--
--   Then for every sequence $\{x^r\}$ generated from $x^0$ by the BCD method using the essentially cyclic rule,
--   $$\text{every cluster point of } \{x^r\} \text{ is a stationary point of } f.$$
--
--   Part (a) of Theorem 4.1 extends results of Grippo–Sciandrone and Zadeh from the differentiable case: it asks only for pseudoconvexity in pairs of blocks, not of $f$ itself.
--
--   **Formalization Note.** "f is continuous on $X^0$" is formalized as continuity of $f$, as a map into $\mathbb R\cup\{\infty\}$, at every point of $X^0$. Read as continuity of the restriction $f|_{X^0}$ only, the printed theorem is false (an explicit two-block counterexample is in the mission description). Blocks are 0-based; `s r` is the block of iteration $r+1$.
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), pp. 480–481, Theorem 4.1(a)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

namespace TsengBCD.Stationary

open Filter Topology

theorem theorem_4_1_a {N : ℕ} [NeZero N] {n : Fin N → ℕ} (f : X n → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (x0 : X n) (hx0 : f x0 ≠ ⊤) (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y) :
    ((∀ i k : Fin N, PseudoconvexIn f {k, i}) → (∀ y ∈ levelSet f x0, IsRegularAt f y) →
      ∀ (s : ℕ → Fin N) (x : ℕ → X n), IsEssCyclic s → x 0 = x0 → IsBCDRun f s x →
        ∀ z, MapClusterPt z atTop x → IsStationary f z) := by sorry

end TsengBCD.Stationary
