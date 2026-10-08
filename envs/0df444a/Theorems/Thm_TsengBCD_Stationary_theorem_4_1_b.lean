-- Prove2me | Theorems.Thm_TsengBCD_Stationary_theorem_4_1_b
-- name    : TsengBCD.Stationary.theorem_4_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T22:18:14.760047+00:00
-- url     : https://prove2.me/theorems/958229d0-0723-476f-af4b-ffe8d1c4b6d4
-- title:
--   Theorem 4.1(b), p. 481 — pseudoconvex in pairs among the first N−1 blocks, regular on X⁰, cyclic rule: cluster points of {x^r}_{r≡(N−1) mod N} are stationary
-- statement:
--   Let $f:\mathbb R^{n_1+\cdots+n_N}\to\mathbb R\cup\{\infty\}$ never take the value $-\infty$, let $f(x^0)<\infty$, and assume that $X^0=\{x: f(x)\le f(x^0)\}$ is compact and that $f$ is continuous on $X^0$. Assume further that
--   1. $f(x_1,\dots,x_N)$ is pseudoconvex in $(x_k,x_i)$ for every $i,k\in\{1,\dots,N-1\}$, and
--   2. $f$ is regular at every $x\in X^0$.
--
--   Then for every sequence $\{x^r\}$ generated from $x^0$ by the BCD method using the cyclic rule,
--   $$\text{every cluster point of } \{x^r\}_{r\equiv(N-1)\bmod N} \text{ is a stationary point of } f,$$
--   where $r\equiv(N-1)\bmod N$ means $r=N-1,2N-1,3N-1,\dots$.
--
--   Part (b) trades a weaker assumption on $f$ (no pseudoconvexity involving block $N$) for a more restrictive block rule.
--
--   **Formalization Note.** Blocks are 0-based: $\{1,\dots,N-1\}$ is the set of Lean indices $k$ with $k<N-1$. The cyclic rule is `s r = r mod N` for the block of iteration $r+1$, and the subsequence is $m\mapsto x^{Nm+(N-1)}$, the iterate just before block $N$ is updated. Continuity is continuity of $f$ at every point of $X^0$ (see Theorem 4.1(a)).
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), pp. 480–481, Theorem 4.1(b)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

namespace TsengBCD.Stationary

open Filter Topology

theorem theorem_4_1_b {N : ℕ} [NeZero N] {n : Fin N → ℕ} (f : X n → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (x0 : X n) (hx0 : f x0 ≠ ⊤) (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y) :
    ((∀ i k : Fin N, i.val < N - 1 → k.val < N - 1 → PseudoconvexIn f {k, i}) →
      (∀ y ∈ levelSet f x0, IsRegularAt f y) →
      ∀ (s : ℕ → Fin N) (x : ℕ → X n), IsCyclic s → x 0 = x0 → IsBCDRun f s x →
        ∀ z, MapClusterPt z atTop (fun m : ℕ => x (N * m + (N - 1))) → IsStationary f z) := by sorry

end TsengBCD.Stationary
