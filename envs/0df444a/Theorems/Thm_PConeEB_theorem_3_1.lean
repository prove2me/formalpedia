-- Prove2me | Theorems.Thm_PConeEB_theorem_3_1
-- name    : PConeEB.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:09.821726+00:00
-- url     : https://prove2.me/theorems/89638349-01ac-432a-ae96-a43e4fd57140
-- title:
--   Theorem 3.1 — optimality of 1-FRFs satisfying (G1)
-- statement:
--   Let $K$ be a closed convex cone, $z\in K^*$ with $\|z\|=1$, and $\mathcal F:=K\cap\{z\}^\perp$ a nontrivial exposed face. Let $\mathfrak g$, $\gamma_{z,\eta}$, $\kappa_{z,\eta}$ be as in Theorem 2.2, with $\gamma_{z,\eta}\in(0,\infty]$ for every $\eta>0$. Let
--   $$
--   \psi_{K,z}(s,t):=s+\kappa_{z,t}\,\mathfrak g(2s),
--   $$
--   so that $\psi_{K,z}$ is a 1-FRF for $K$ and $z$. Suppose further that (SH) and (G1) hold. For $\bar\eta>0$ define
--   $$
--   M(t):=\frac12\left[1+\kappa_{z,\bar\eta}\cdot\left(\max\left\{1,\frac{\|\bar v\|}{t}\right\}L_{\mathfrak g}\right)\right]^{-1},
--   $$
--   where $\bar v$ and $L_{\mathfrak g}$ are as in (G1). Let $\psi^\star_{K,z}$ be an arbitrary 1-FRF for $K$ and $z$. Then for any $\bar\eta_0\in(0,\bar\eta]$ there exists $s_0>0$ such that
--   $$
--   M(\bar\eta_0)\,\psi_{K,z}(s,b)\le\psi^\star_{K,z}(s,\bar\eta_0)\qquad\forall(s,b)\in[0,s_0]\times[0,\bar\eta].
--   $$
--
--   Up to a constant, no 1-FRF for $K$ and $z$ improves on one built from a $\mathfrak g$ that satisfies (G1).
--
--   Differences from the source:
--   - encoding: "so that ψ is a 1-FRF" in the hypotheses → a first conclusion IsOneStepFRF K z ψ; reason: the page derives it from Lemma 2.3; asserting it gives the sentence its content
--   - reading: ∂K, "the boundary" of K, for K possibly lower dimensional → frontier K, the topological boundary in E, inside gammaZ; reason: frontier K contains every relative boundary point, so the infimum runs over at least the same v; the proof of Theorem 2.2 needs exactly this, since the projection of q ∉ span K onto K can lie in ri K. For full-dimensional K the two notions coincide
--   - encoding: γ_{z,η} ∈ (0, ∞], with inf ∅ = +∞ → gammaZ in ENNReal, 0 < gammaZ K z g η; κ_{z,η} the real number kappaZ, with γ⁻¹ read as 0 at γ = ⊤; reason: the paper's own convention γ_{z,0} = ∞; kappaZ is used only under 0 < gammaZ
--   - encoding: (G1): w : (0, 1] → {z}^⊥ ∩ span K \ F continuous, L_g = limsup < ∞ → SatisfiesG1 with a total w, the conditions on Set.Ioc 0 1, and an ENNReal limsup equal to ENNReal.ofReal Lg with 0 ≤ Lg; reason: Lean conventions; same instances, and an ENNReal limsup has no boundedness side condition
--   - encoding: g : ℝ₊ → ℝ₊ and dist(·, C) → g : ℝ → ℝ with its conditions on Set.Ici 0 only, and Metric.infDist on nonempty sets; reason: Lean conventions; the same instances
--   - encoding: a finite dimensional Euclidean space E → a type E with InnerProductSpace ℝ E, FiniteDimensional ℝ E and CompleteSpace E; reason: Mathlib conventions; CompleteSpace is required by ProperCone.innerDual and holds in every finite dimensional space
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Theorem 3.1, (3.2)–(3.4), p.12

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_PConeEB_IsNontrivialFace
import Definitions.Def_PConeEB_hyperplane
import Definitions.Def_PConeEB_IsOneStepFRF
import Definitions.Def_PConeEB_kappaZ
import Definitions.Def_PConeEB_SatisfiesSH
import Definitions.Def_PConeEB_SatisfiesG1

open MoreauProx.Decomposition (IsClosedConvexCone)

namespace PConeEB

/-- Theorem 3.1 (optimality of 1-FRFs satisfying (G1)). Let `K` be a closed convex cone, `z ∈ K*` with
`‖z‖ = 1`, `F := K ∩ {z}^⊥` a nontrivial exposed face, and `g, γ_{z,η}, κ_{z,η}` as in Theorem 2.2 with
`γ_{z,η} ∈ (0, ∞]` for every `η > 0`. Let `ψ(s, t) := s + κ_{z,t} g(2 s)`, a 1-FRF for `K` and `z`,
and suppose (SH) and (G1). For `η̄ > 0` let
`M(t) := (1/2) [1 + κ_{z,η̄} (max{1, ‖v̄‖/t} L_g)]⁻¹`. Then for every 1-FRF `ψ⋆` for `K` and `z` and
every `η̄₀ ∈ (0, η̄]` there is `s₀ > 0` with `M(η̄₀) ψ(s, b) ≤ ψ⋆(s, η̄₀)` for all
`(s, b) ∈ [0, s₀] × [0, η̄]`. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Theorem 3.1,
(3.2)–(3.4), p.12.

**Formalization Note.** The sentence "so that `ψ` is a 1-FRF" is the first conclusion. `s₀` may
depend on `η̄`, `ψ⋆` and `η̄₀`. `M` uses `κ` at `η̄`, not at `t`. `[CompleteSpace E]` is needed by
`ProperCone.innerDual` and is automatic in finite dimension. -/
theorem theorem_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {K : Set E} (hK : IsClosedConvexCone K)
    {z : E} (hz : z ∈ ProperCone.innerDual K) (hznorm : ‖z‖ = 1)
    (hF : IsNontrivialFace K (K ∩ hyperplane z))
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) {g : ℝ → ℝ}
    (hgmono : MonotoneOn g (Set.Ici 0)) (hg0 : g 0 = 0)
    (hgα : ∀ t, 0 ≤ t → t ^ α ≤ g t)
    (hγ : ∀ η, 0 < η → 0 < gammaZ K z g η)
    (hSH : SatisfiesSH g)
    {v : E} {w : ℝ → E} {Lg : ℝ} (hG1 : SatisfiesG1 K z g v w Lg) :
    IsOneStepFRF K z (fun s t => s + kappaZ K z g α t * g (2 * s)) ∧
    ∀ ηbar : ℝ, 0 < ηbar → ∀ ψstar : ℝ → ℝ → ℝ, IsOneStepFRF K z ψstar →
      ∀ ηbar₀ : ℝ, 0 < ηbar₀ → ηbar₀ ≤ ηbar →
        ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s ∈ Set.Icc 0 s₀, ∀ b ∈ Set.Icc 0 ηbar,
          (1 / 2) * (1 + kappaZ K z g α ηbar * (max 1 (‖v‖ / ηbar₀) * Lg))⁻¹ *
              (s + kappaZ K z g α b * g (2 * s)) ≤ ψstar s ηbar₀ := by sorry

end PConeEB
