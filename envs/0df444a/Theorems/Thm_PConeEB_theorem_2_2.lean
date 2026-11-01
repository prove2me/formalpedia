-- Prove2me | Theorems.Thm_PConeEB_theorem_2_2
-- name    : PConeEB.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:40.693652+00:00
-- url     : https://prove2.me/theorems/8c21dc57-7188-4345-a026-543173c5c6cc
-- title:
--   Theorem 2.2 — $\gamma_{z,\eta}>0$ iff a $\mathfrak g$-error bound holds on $\{z\}^\perp\cap B(\eta)$
-- statement:
--   Let $K$ be a closed convex cone and $z\in K^*$ such that $\mathcal F=\{z\}^\perp\cap K$ is a nontrivial exposed face. Let $\eta\ge0$, $\alpha\in(0,1]$, and let $\mathfrak g:\mathbb R_+\to\mathbb R_+$ be nondecreasing with $\mathfrak g(0)=0$ and $\mathfrak g\ge|\cdot|^\alpha$. Let $\gamma_{z,\eta}$ be as in (2.13).
--
--   1. If $\gamma_{z,\eta}\in(0,\infty]$, then
--   $$
--   \operatorname{dist}(q,\mathcal F)\le\kappa_{z,\eta}\,\mathfrak g(\operatorname{dist}(q,K))\quad\text{whenever }q\in\{z\}^\perp\cap B(\eta),
--   $$
--   where $\kappa_{z,\eta}:=\max\{2\eta^{1-\alpha},2\gamma_{z,\eta}^{-1}\}<\infty$.
--   2. Conversely, if there exists $\kappa_B\in(0,\infty)$ with $\operatorname{dist}(q,\mathcal F)\le\kappa_B\,\mathfrak g(\operatorname{dist}(q,K))$ whenever $q\in\{z\}^\perp\cap B(\eta)$, then $\gamma_{z,\eta}\in(0,\infty]$.
--
--   The theorem reduces a uniform error bound on the hyperplane to a positivity statement about a single infimum. The paper cites it from Lindstrom, Lourenço and Pong (2022), Theorem 3.10.
--
--   Differences from the source:
--   - reading: ∂K, "the boundary" of K, for K possibly lower dimensional → frontier K, the topological boundary in E, inside gammaZ; reason: frontier K contains every relative boundary point, so the infimum runs over at least the same v; the proof of Theorem 2.2 needs exactly this, since the projection of q ∉ span K onto K can lie in ri K. For full-dimensional K the two notions coincide
--   - encoding: γ_{z,η} ∈ (0, ∞], with inf ∅ = +∞ → gammaZ in ENNReal, 0 < gammaZ K z g η; κ_{z,η} the real number kappaZ, with γ⁻¹ read as 0 at γ = ⊤; reason: the paper's own convention γ_{z,0} = ∞; kappaZ is used only under 0 < gammaZ
--   - encoding: g : ℝ₊ → ℝ₊ and dist(·, C) → g : ℝ → ℝ with its conditions on Set.Ici 0 only, and Metric.infDist on nonempty sets; reason: Lean conventions; the same instances
--   - encoding: a finite dimensional Euclidean space E → a type E with InnerProductSpace ℝ E, FiniteDimensional ℝ E and CompleteSpace E; reason: Mathlib conventions; CompleteSpace is required by ProperCone.innerDual and holds in every finite dimensional space
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Theorem 2.2, (2.13)–(2.14), p.8

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_PConeEB_IsNontrivialFace
import Definitions.Def_PConeEB_hyperplane
import Definitions.Def_PConeEB_gammaZ
import Definitions.Def_PConeEB_kappaZ

open MoreauProx.Decomposition (IsClosedConvexCone)

namespace PConeEB

/-- Theorem 2.2. Let `K` be a closed convex cone, `z ∈ K*` with `F = {z}^⊥ ∩ K` a nontrivial exposed
face, `η ≥ 0`, `α ∈ (0, 1]`, and `g : ℝ₊ → ℝ₊` nondecreasing with `g(0) = 0`, `g ≥ |·|^α`.
(i) If `γ_{z,η} ∈ (0, ∞]` then `dist(q, F) ≤ κ_{z,η} g(dist(q, K))` for `q ∈ {z}^⊥ ∩ B(η)`.
(ii) If such a bound holds with some `κ_B ∈ (0, ∞)`, then `γ_{z,η} ∈ (0, ∞]`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Theorem 2.2, (2.13)–(2.14), p.8 (from Lindstrom,
Lourenço & Pong, Error bounds, facial residual functions and applications to the exponential cone,
Theorem 3.10).

**Formalization Note.** `κ_{z,η} < ∞` is automatic for a real number. `∂K` inside `gammaZ` is
`frontier K`. `g` is a function on `ℝ` with its conditions on `Set.Ici 0`. `[CompleteSpace E]` is
needed by `ProperCone.innerDual` and is automatic in finite dimension. -/
theorem theorem_2_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {K : Set E} (hK : IsClosedConvexCone K)
    {z : E} (hz : z ∈ ProperCone.innerDual K)
    (hF : IsNontrivialFace K (K ∩ hyperplane z))
    {η α : ℝ} (hη : 0 ≤ η) (hα₀ : 0 < α) (hα₁ : α ≤ 1) {g : ℝ → ℝ}
    (hgmono : MonotoneOn g (Set.Ici 0)) (hg0 : g 0 = 0)
    (hgα : ∀ t, 0 ≤ t → t ^ α ≤ g t) :
    (0 < gammaZ K z g η →
      ∀ q ∈ hyperplane z, ‖q‖ ≤ η →
        Metric.infDist q (K ∩ hyperplane z) ≤
          kappaZ K z g α η * g (Metric.infDist q K)) ∧
    ((∃ κB : ℝ, 0 < κB ∧ ∀ q ∈ hyperplane z, ‖q‖ ≤ η →
        Metric.infDist q (K ∩ hyperplane z) ≤ κB * g (Metric.infDist q K)) →
      0 < gammaZ K z g η) := by sorry

end PConeEB
