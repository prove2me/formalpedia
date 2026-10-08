-- Prove2me | Theorems.Thm_ProgHedging_Convex_proposition_4_5
-- name    : ProgHedging.Convex.proposition_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:29:23.352723+00:00
-- url     : https://prove2.me/theorems/cb664610-16b4-4da9-8232-e3234a66d011
-- title:
--   Proposition 4.5 — Φ is lower semicontinuous with compact level sets on ℳ, Φ(0) = min (P), min Φ = α̂, and Φ is convex in the convex case
-- statement:
--   Let $\Phi(U)=\min\{F(X)\mid X\in\mathcal C,\ KX=U\}$ for $U\in\mathcal M$, with $\Phi(U)=+\infty$ when no such $X$ exists. Then:
--
--   1. $\Phi$ is lower semicontinuous on $\mathcal M$, and every level set $\{U\in\mathcal M\mid\Phi(U)\le\alpha\}$, $\alpha\in\mathbb R$, is compact;
--   2. $\Phi(0)=\min(P)$, interpreted as $+\infty$ if $\mathcal C\cap\mathcal N=\emptyset$;
--   3. $\min_{U\in\mathcal M}\Phi(U)=\hat\alpha$, the minimum being attained;
--   4. in the convex case $\Phi$ is convex on $\mathcal M$, i.e. its epigraph $\{(U,\beta)\in\mathcal M\times\mathbb R\mid \Phi(U)\le\beta\}$ is convex.
--
--   $\Phi$ is the value of the problem with the implementability constraint $KX=0$ relaxed to $KX=U$; the dual problem (D) is its conjugate dual.
--
--   **Formalization Note.** $\Phi$ takes values in `EReal`. Convexity of an extended-real function on $\mathcal M$ is stated as convexity of its epigraph over $\mathcal M$, as in the paper's proof. The printed reference "the value in Proposition 2.1" means Proposition 3.1.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 18, Proposition 4.5, (4.22)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Convex_Duality
open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- Proposition 4.5, p. 18. `Φ` is lower semicontinuous on `ℳ`, with compact level sets
`{U ∈ ℳ | Φ(U) ≤ α}`; `Φ(0) = min (P)` (`∞` if `𝒞 ∩ 𝒩 = ∅`); `min_{U ∈ ℳ} Φ(U) = α̂` (attained);
and in the convex case `Φ` is convex on `ℳ` (its epigraph over `ℳ` is convex). -/
theorem proposition_4_5 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) :
    LowerSemicontinuousOn pr.Phi pr.M ∧
    (∀ α : ℝ, IsCompact {U | U ∈ pr.M ∧ pr.Phi U ≤ (α : EReal)}) ∧
    pr.Phi 0 = pr.minP ∧
    (∃ U ∈ pr.M, pr.Phi U = pr.alphaHat) ∧ (∀ U ∈ pr.M, pr.alphaHat ≤ pr.Phi U) ∧
    (pr.ConvexCase →
      Convex ℝ {q : Policy S n × ℝ | q.1 ∈ pr.M ∧ pr.Phi q.1 ≤ (q.2 : EReal)}) := by sorry

end ProgHedging.Convex
