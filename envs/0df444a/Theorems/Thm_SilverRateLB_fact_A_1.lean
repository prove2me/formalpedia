-- Prove2me | Theorems.Thm_SilverRateLB_fact_A_1
-- name    : SilverRateLB.fact_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:47.939694+00:00
-- url     : https://prove2.me/theorems/6baaeb14-e0b1-49ad-9f88-f7e41c815e3a
-- title:
--   Fact A.1 — Moreau envelopes; $\nabla\mathrm{env}_1\sigma_K=\Pi_K$; same zero set
-- statement:
--   Let $g:\mathbb R^d\to(-\infty,+\infty]$ be proper, closed and convex, with Moreau envelope and proximal map
--   $$\mathrm{env}_1g(x):=\min_{y}\Bigl\{g(y)+\tfrac12\|x-y\|^2\Bigr\},\qquad \mathrm{prox}_g(x):=\arg\min_y\Bigl\{g(y)+\tfrac12\|x-y\|^2\Bigr\}.$$
--   Then:
--   1. $\mathrm{env}_1g$ is finite and the minimum is attained;
--   2. $\mathrm{env}_1g$ is convex and continuously differentiable;
--   3. its gradient is $1$-Lipschitz and $\nabla\mathrm{env}_1g(x)=x-\mathrm{prox}_g(x)$;
--   4. if $g\ge0$, then $\mathrm{env}_1g\ge0$ and $\mathrm{env}_1g(x)=0$ exactly when $g(x)=0$;
--   5. for every nonempty closed convex $K\subseteq\mathbb R^d$ with support function $\sigma_K(x)=\sup_{v\in K}\langle v,x\rangle$,
--   $$\nabla\mathrm{env}_1\sigma_K(x)=\Pi_K(x).$$
--
--   The proof of Lemma 3.2 realizes the local hard function as the Moreau envelope of a finite maximum of affine functions, a support function after translation, and reads its gradient off item 5.
--
--   **Formalization Note** $g$ is extended-real valued; "proper, closed, convex" is the published `MoreauProx.Characterization.GammaZero`, $\mathrm{env}_1$ is the published extended-real infimum `NonsmoothLojasiewicz.Convex.moreauEnv` and $\mathrm{prox}_g$ the published `MoreauProx.Characterization.prox`, $\sigma_K$ the published extended-real `DualRCD.suppFn` and $\Pi_K$ the published predicate `OrabonaOL.OGD.IsEuclideanProj`. The differentiability statements are about the real-valued envelope, which item 1 makes legitimate.
--
--   Differences from the source:
--   - encoding: env_1 g(x) := min_y {…} (a real minimum) → the EReal infimum moreauEnv, with “finite and attained” as a clause; derivatives of its toReal; reason: the min notation presupposes attainment, which the clause states
--   - encoding: proper, closed, convex g : ℝ^d → (−∞, +∞] → GammaZero g with g : EuclideanSpace ℝ (Fin d) → EReal; reason: same functions
--   - encoding: continuously differentiable → ContDiff ℝ 1; reason: same notion
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Fact A.1, p. 24

import Mathlib
import Definitions.Def_DualRCD_suppFn
import Definitions.Def_NonsmoothLojasiewicz_Convex_moreauEnv
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_MoreauProx_Characterization_Prox
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj

namespace SilverRateLB

open NonsmoothLojasiewicz.Convex MoreauProx.Characterization

/-- **Fact A.1 (Moreau envelopes).** Let `g : ℝ^d → (−∞, +∞]` be proper, closed and convex, with
Moreau envelope `env₁ g(x) = min_y {g(y) + ½‖x − y‖²}` and proximal map `prox_g`. Then
`env₁ g` is finite (the minimum is attained), convex and continuously differentiable, its
gradient is `1`-Lipschitz and `∇env₁ g(x) = x − prox_g(x)`; if `g ≥ 0` then `env₁ g ≥ 0` and the
two functions have the same zero set. Moreover, for every nonempty closed convex `K ⊆ ℝ^d` with
support function `σ_K`, `∇env₁ σ_K(x) = Π_K(x)`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Fact A.1, p. 24.

**Formalization Note** `g` is `EReal`-valued and "proper, closed, convex" is
`MoreauProx.Characterization.GammaZero g` (never `⊥`, not identically `⊤`, convex epigraph,
lower semicontinuous). `env₁ g` is the `EReal` infimum `NonsmoothLojasiewicz.Convex.moreauEnv g`;
its finiteness and attainment are the first clause, and the real function studied is its
`toReal`. `prox_g` is `MoreauProx.Characterization.prox g`. `σ_K` is the published `DualRCD.suppFn K` (in
`EReal`, `+∞` allowed for unbounded `K`) and `Π_K(x) = p` is `IsEuclideanProj K x p`. -/
theorem fact_A_1 {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → EReal) (hg : GammaZero g) :
    (∀ x, moreauEnv g x ≠ ⊥ ∧ moreauEnv g x ≠ ⊤ ∧
      ∃ y, moreauEnv g x = g y + (((‖x - y‖ ^ 2) / 2 : ℝ) : EReal)) ∧
    ConvexOn ℝ Set.univ (fun x => (moreauEnv g x).toReal) ∧
    ContDiff ℝ 1 (fun x => (moreauEnv g x).toReal) ∧
    (∀ x y, ‖gradient (fun x => (moreauEnv g x).toReal) x -
        gradient (fun x => (moreauEnv g x).toReal) y‖ ≤ ‖x - y‖) ∧
    (∀ x, gradient (fun x => (moreauEnv g x).toReal) x = x - prox g x) ∧
    ((∀ x, 0 ≤ g x) → ∀ x, 0 ≤ moreauEnv g x ∧ (moreauEnv g x = 0 ↔ g x = 0)) ∧
    (∀ K : Set (EuclideanSpace ℝ (Fin d)), K.Nonempty → IsClosed K → Convex ℝ K →
      ∀ x, OrabonaOL.OGD.IsEuclideanProj K x
        (gradient (fun x => (moreauEnv (DualRCD.suppFn K) x).toReal) x)) := by sorry

end SilverRateLB
