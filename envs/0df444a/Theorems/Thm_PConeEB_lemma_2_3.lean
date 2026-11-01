-- Prove2me | Theorems.Thm_PConeEB_lemma_2_3
-- name    : PConeEB.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:02.98212+00:00
-- url     : https://prove2.me/theorems/cd9bf8fc-5b85-42d5-ac33-a96e6cb6f2da
-- title:
--   Lemma 2.3 — a bound on $\{z\}^\perp$ yields a 1-FRF
-- statement:
--   Let $K$ be a closed convex cone and $z\in K^*$ such that $\mathcal F=\{z\}^\perp\cap K$ is a proper face. Let $\mathfrak g:\mathbb R_+\to\mathbb R_+$ be nondecreasing with $\mathfrak g(0)=0$, and let $\kappa_{z,s}$ be a finite, nondecreasing, nonnegative function of $s\in\mathbb R_+$ such that
--   $$
--   \operatorname{dist}(q,\mathcal F)\le\kappa_{z,\|q\|}\,\mathfrak g(\operatorname{dist}(q,K))\quad\text{whenever }q\in\{z\}^\perp.
--   $$
--   Define $\psi_{K,z}(s,t):=\max\{s,s/\|z\|\}+\kappa_{z,t}\,\mathfrak g(s+\max\{s,s/\|z\|\})$. Then
--   $$
--   \operatorname{dist}(p,\mathcal F)\le\psi_{K,z}(\epsilon,\|p\|)\quad\text{whenever }\operatorname{dist}(p,K)\le\epsilon\text{ and }\langle p,z\rangle\le\epsilon,
--   $$
--   and $\psi_{K,z}$ is a 1-FRF for $K$ and $z$.
--
--   The paper cites this lemma from Lindstrom, Lourenço and Pong (2022), Lemma 3.9.
--
--   Differences from the source:
--   - encoding: κ_{z,s} a finite function of s; the point p in (2.12) → κ : ℝ → ℝ with its conditions on Set.Ici 0; the point is called x, since p is the cone parameter elsewhere; reason: Lean conventions; the same instances
--   - encoding: g : ℝ₊ → ℝ₊ and dist(·, C) → g : ℝ → ℝ with its conditions on Set.Ici 0 only, and Metric.infDist on nonempty sets; reason: Lean conventions; the same instances
--   - encoding: a finite dimensional Euclidean space E → a type E with InnerProductSpace ℝ E, FiniteDimensional ℝ E and CompleteSpace E; reason: Mathlib conventions; CompleteSpace is required by ProperCone.innerDual and holds in every finite dimensional space
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Lemma 2.3, (2.11)–(2.12), p.8

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_PConeEB_hyperplane
import Definitions.Def_PConeEB_IsOneStepFRF
import Definitions.Def_PConeEB_lemma23FRF

open MoreauProx.Decomposition (IsClosedConvexCone)

namespace PConeEB

/-- Lemma 2.3. Let `K` be a closed convex cone, `z ∈ K*` with `F = {z}^⊥ ∩ K` proper, `g : ℝ₊ → ℝ₊`
nondecreasing with `g(0) = 0`, and `κ` finite, nondecreasing and nonnegative on `ℝ₊`, with
`dist(q, F) ≤ κ_{‖q‖} g(dist(q, K))` for `q ∈ {z}^⊥`. Then
`ψ(s, t) := max{s, s/‖z‖} + κ_t g(s + max{s, s/‖z‖})` satisfies
`dist(p, F) ≤ ψ(ε, ‖p‖)` whenever `dist(p, K) ≤ ε` and `⟨p, z⟩ ≤ ε`, and `ψ` is a 1-FRF for `K`
and `z`. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Lemma 2.3, (2.11)–(2.12), p.8 (from
Lindstrom, Lourenço & Pong, Error bounds, facial residual functions and applications to the
exponential cone, Lemma 3.9).

**Formalization Note.** (2.12) is for every `x : E`, not only `x ∈ span K`. The paper's `p` is `x`
here. `κ` is real valued, so finite. `[CompleteSpace E]` is needed by `ProperCone.innerDual` and is
automatic in finite dimension. -/
theorem lemma_2_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {K : Set E} (hK : IsClosedConvexCone K)
    {z : E} (hz : z ∈ ProperCone.innerDual K) (hproper : K ∩ hyperplane z ≠ K)
    {g κ : ℝ → ℝ} (hgmono : MonotoneOn g (Set.Ici 0)) (hg0 : g 0 = 0)
    (hκmono : MonotoneOn κ (Set.Ici 0)) (hκnonneg : ∀ s, 0 ≤ s → 0 ≤ κ s)
    (hbound : ∀ q ∈ hyperplane z,
      Metric.infDist q (K ∩ hyperplane z) ≤ κ ‖q‖ * g (Metric.infDist q K)) :
    (∀ (x : E) (ε : ℝ), Metric.infDist x K ≤ ε → inner ℝ x z ≤ ε →
      Metric.infDist x (K ∩ hyperplane z) ≤ lemma23FRF z κ g ε ‖x‖) ∧
    IsOneStepFRF K z (lemma23FRF z κ g) := by sorry

end PConeEB
