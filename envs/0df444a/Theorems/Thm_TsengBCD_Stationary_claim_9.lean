-- Prove2me | Theorems.Thm_TsengBCD_Stationary_claim_9
-- name    : TsengBCD.Stationary.claim_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T22:18:22.787434+00:00
-- url     : https://prove2.me/theorems/9a9033f8-26f8-4ff2-a8a5-fac0c58e6235
-- title:
--   Proof of Theorem 4.1(a), (b), p. 482, claim (9) — under block pseudoconvexity and regularity, z^j minimizes f in each block s¹, …, s^j
-- statement:
--   Let $f:\mathbb R^{n_1+\cdots+n_N}\to\mathbb R\cup\{\infty\}$ never take the value $-\infty$, let $f(x^0)<\infty$, $X^0=\{x: f(x)\le f(x^0)\}$, and $T\ge 0$. Let $z^1,\dots,z^T$ be points and $s^1,\dots,s^T$ blocks such that:
--   1. $f$ is regular at every point of $X^0$;
--   2. $f$ is pseudoconvex in $(x_k,x_i)$ for every $i,k\in\{s^1\}\cup\cdots\cup\{s^{T-1}\}$;
--   3. (6) $z^j\in X^0$ and $f(z^j)=f(z^1)$ for $j=1,\dots,T$;
--   4. (7) $f(z^j)\le f(z^j+(0,\dots,d_{s^j},\dots,0))$ for all $d_{s^j}$, $j=1,\dots,T$, and $z^j_k=z^{j-1}_k$ for all $k\ne s^j$, $j=2,\dots,T$;
--   5. (8) $f(z^{j-1})\le f(z^{j-1}+(0,\dots,d_{s^j},\dots,0))$ for all $d_{s^j}$, $j=2,\dots,T$.
--
--   Then for $j=1,\dots,T-1$,
--   $$f(z^j)\le f(z^j+(0,\dots,d_k,\dots,0))\qquad\forall d_k,\ \forall k=s^1,\dots,s^j.\tag{9}$$
--
--   Claim (9) is the core of parts (a) and (b) of Theorem 4.1: with $z^{T-1}=z$ it shows that the cluster point $z$ minimizes $f$ in each of the blocks $s^1,\dots,s^{T-1}$.
--
--   **Formalization Note.** The claim is stated about the points $z^j$ and blocks $s^j$ alone, with (6), (7), (8) as hypotheses; the item `limit_chain` produces them from a BCD run. Indices $j$ are natural numbers and $s^j$ are 0-based blocks. "Pseudoconvex in $(x_k,x_i)$" is pseudoconvexity in the set of blocks $\{k,i\}$ ($k=i$ allowed).
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), p. 482, proof of Theorem 4.1(a), (b), claim (9)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

namespace TsengBCD.Stationary

open Filter Topology

theorem claim_9 {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (x0 : X n) (hx0 : f x0 ≠ ⊤) (T : ℕ) (zs : ℕ → X n) (ss : ℕ → Fin N)
    (hreg : ∀ y ∈ levelSet f x0, IsRegularAt f y)
    (hpc : ∀ i j, 1 ≤ i → i ≤ T - 1 → 1 ≤ j → j ≤ T - 1 → PseudoconvexIn f {ss i, ss j})
    (h6 : ∀ j, 1 ≤ j → j ≤ T → zs j ∈ levelSet f x0 ∧ f (zs j) = f (zs 1))
    (h7 : ∀ j, 1 ≤ j → j ≤ T → ∀ d : EuclideanSpace ℝ (Fin (n (ss j))),
      f (zs j) ≤ f (zs j + Pi.single (ss j) d))
    (h7' : ∀ j, 2 ≤ j → j ≤ T → ∀ k : Fin N, k ≠ ss j → zs j k = zs (j - 1) k)
    (h8 : ∀ j, 2 ≤ j → j ≤ T → ∀ d : EuclideanSpace ℝ (Fin (n (ss j))),
      f (zs (j - 1)) ≤ f (zs (j - 1) + Pi.single (ss j) d)) :
    ∀ j, 1 ≤ j → j ≤ T - 1 → ∀ l, 1 ≤ l → l ≤ j →
      ∀ d : EuclideanSpace ℝ (Fin (n (ss l))), f (zs j) ≤ f (zs j + Pi.single (ss l) d) := by sorry

end TsengBCD.Stationary
