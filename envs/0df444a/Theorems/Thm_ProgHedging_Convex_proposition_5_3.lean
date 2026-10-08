-- Prove2me | Theorems.Thm_ProgHedging_Convex_proposition_5_3
-- name    : ProgHedging.Convex.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:29.361013+00:00
-- url     : https://prove2.me/theorems/2255a4ea-3463-4cc5-a6c8-6ff04a13183f
-- title:
--   Proposition 5.3 — each iteration of progressive hedging is the unique saddle point of ℓ(V, W) + (r/2)‖V − X̂^ν‖² − (1/2r)‖W − W^ν‖²
-- statement:
--   Consider the progressive hedging algorithm in the convex case with exact minimization and $r>0$, generating $X^\nu$, $\hat X^\nu=JX^\nu$ and $W^\nu$. Let
--
--   $$
--   \ell(V,W)=\inf\{F(X)+\langle X,W\rangle\mid X\in\mathcal C,\ \hat X=V\}\qquad (V\in\mathcal N,\ W\in\mathcal M).
--   $$
--
--   Then for every $\nu$, the pair $(\hat X^{\nu+1},W^{\nu+1})\in\mathcal N\times\mathcal M$ is the unique saddle point of
--
--   $$
--   \Psi^\nu(V,W)=\ell(V,W)+\frac r2\|V-\hat X^\nu\|^2-\frac1{2r}\|W-W^\nu\|^2
--   $$
--
--   with respect to minimizing over $V\in\mathcal N$ and maximizing over $W\in\mathcal M$: $\Psi^\nu(\hat X^{\nu+1},W)\le\Psi^\nu(\hat X^{\nu+1},W^{\nu+1})\le\Psi^\nu(V,W^{\nu+1})$ for all such $V,W$, and any other pair with this property equals $(\hat X^{\nu+1},W^{\nu+1})$.
--
--   This exhibits the algorithm as a proximal point iteration on the saddle function $\ell$.
--
--   **Formalization Note.** $\ell$ and $\Psi^\nu$ take values in `EReal` ($\ell=+\infty$ when no admissible $X$ has $\hat X=V$); adding a real number to an extended real is unambiguous.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 26, Proposition 5.3, (5.31)–(5.32)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Convex_Duality
import Definitions.Def_ProgHedging_Convex_Algorithm
open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- Proposition 5.3, p. 26. For the algorithm in the convex case with exact minimization, at every
iteration `ν`, `(X̂^{ν+1}, W^{ν+1})` is the unique saddle point, relative to minimizing over `V ∈ 𝒩` and
maximizing over `U ∈ ℳ`, of
`Ψ(V, U) = ℓ(V, U) + (r/2)‖V − X̂^ν‖² − (1/2r)‖U − W^ν‖²` (5.32), with `ℓ` as in (5.31). -/
theorem proposition_5_3 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r) (X W : ℕ → Policy S n)
    (hseq : pr.IsExactPHSeq r X W) (ν : ℕ) :
    let Ψ : Policy S n → Policy S n → EReal := fun V U =>
      pr.ell V U + ((r / 2 * pr.pnorm (V - pr.J (X ν)) ^ 2 -
        1 / (2 * r) * pr.pnorm (U - W ν) ^ 2 : ℝ) : EReal)
    pr.J (X (ν + 1)) ∈ pr.N ∧ W (ν + 1) ∈ pr.M ∧
    (∀ V ∈ pr.N, ∀ U ∈ pr.M,
      Ψ (pr.J (X (ν + 1))) U ≤ Ψ (pr.J (X (ν + 1))) (W (ν + 1)) ∧
      Ψ (pr.J (X (ν + 1))) (W (ν + 1)) ≤ Ψ V (W (ν + 1))) ∧
    ∀ V' ∈ pr.N, ∀ U' ∈ pr.M,
      (∀ V ∈ pr.N, ∀ U ∈ pr.M, Ψ V' U ≤ Ψ V' U' ∧ Ψ V' U' ≤ Ψ V U') →
      V' = pr.J (X (ν + 1)) ∧ U' = W (ν + 1) := by sorry

end ProgHedging.Convex
