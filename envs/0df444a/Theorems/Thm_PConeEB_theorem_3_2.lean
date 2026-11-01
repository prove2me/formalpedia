-- Prove2me | Theorems.Thm_PConeEB_theorem_3_2
-- name    : PConeEB.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:58.665366+00:00
-- url     : https://prove2.me/theorems/88887ffd-2f33-40cc-ab7b-122b2084c8b9
-- title:
--   Theorem 3.2 — best error bounds
-- statement:
--   Suppose (Feas) is feasible, and assume:
--
--   1. there are $z\in K^*\cap\mathcal L^\perp\cap\{a\}^\perp$ and $\mathcal F:=K\cap\{z\}^\perp$ such that $\mathcal F$ is a nontrivial exposed face and $\{\mathcal F,\mathcal L+a\}$ satisfies the PPS condition;
--   2. $\psi$ is the 1-FRF of Lemma 2.3 for $\mathfrak g$ and $\kappa_{z,\eta}$ as in Theorem 2.2, with $\gamma_{z,\eta}\in(0,\infty]$ for every $\eta>0$;
--   3. $\mathfrak g$ satisfies (SH), and (G1) holds.
--
--   Then:
--
--   (a) There is a positively rescaled shift $\hat\psi$ of $\psi$ such that for any bounded set $B$ there is $\kappa_B>0$ such that for every $x\in B$ and $\epsilon\ge0$,
--   $$
--   \operatorname{dist}(x,K)\le\epsilon\text{ and }\operatorname{dist}(x,\mathcal L+a)\le\epsilon\ \Longrightarrow\ \operatorname{dist}(x,(\mathcal L+a)\cap K)\le\kappa_B(\epsilon+\hat\psi(\epsilon,\tilde\eta)),
--   $$
--   where $\tilde\eta=\sup_{x\in B}\|x\|$.
--
--   (b) Suppose also $\|z\|=1$, $\mathcal L=\{z\}^\perp$ and $a=0$. Then for any consistent error bound function $\Phi$ for $K,\mathcal L$ and any $\hat\eta>0$ there are $\hat\kappa>0$ and $s_0>0$ such that
--   $$
--   s+\hat\psi(s,\hat\eta)\le\hat\kappa\,\Phi(\hat\kappa s,\hat\eta)\qquad\forall s\in[0,s_0].
--   $$
--
--   When a single facial reduction step suffices and the 1-FRF is built from a $\mathfrak g$ satisfying (G1), the resulting error bound is optimal among all consistent error bound functions.
--
--   Differences from the source:
--   - generalization: item (b) for the ψ̂ of item (a) → item (b) for every positively rescaled shift ψ̂ of ψ; reason: the proof of (b) uses only (2.5), and the ψ̂ of (a) is one such shift, so the printed form follows
--   - generalization: K = K¹ × K² in PPS (iii) → K = K₁ + K₂ with K₁ ⊆ E₁, K₂ ⊆ E₂ for complementary subspaces E₁, E₂, not necessarily orthogonal; reason: orthogonal subspaces are the Cartesian case, so the hypothesis is weaker and the result covers the source; a linear isomorphism preserves polyhedrality, ri and Lipschitzian error bounds up to constants
--   - reading: ∂K, "the boundary" of K, for K possibly lower dimensional → frontier K, the topological boundary in E, inside gammaZ; reason: frontier K contains every relative boundary point, so the infimum runs over at least the same v; the proof of Theorem 2.2 needs exactly this, since the projection of q ∉ span K onto K can lie in ri K. For full-dimensional K the two notions coincide
--   - encoding: γ_{z,η} ∈ (0, ∞], with inf ∅ = +∞ → gammaZ in ENNReal, 0 < gammaZ K z g η; κ_{z,η} the real number kappaZ, with γ⁻¹ read as 0 at γ = ⊤; reason: the paper's own convention γ_{z,0} = ∞; kappaZ is used only under 0 < gammaZ
--   - encoding: (G1): w : (0, 1] → {z}^⊥ ∩ span K \ F continuous, L_g = limsup < ∞ → SatisfiesG1 with a total w, the conditions on Set.Ioc 0 1, and an ENNReal limsup equal to ENNReal.ofReal Lg with 0 ≤ Lg; reason: Lean conventions; same instances, and an ENNReal limsup has no boundedness side condition
--   - encoding: g : ℝ₊ → ℝ₊ and dist(·, C) → g : ℝ → ℝ with its conditions on Set.Ici 0 only, and Metric.infDist on nonempty sets; reason: Lean conventions; the same instances
--   - encoding: a finite dimensional Euclidean space E → a type E with InnerProductSpace ℝ E, FiniteDimensional ℝ E and CompleteSpace E; reason: Mathlib conventions; CompleteSpace is required by ProperCone.innerDual and holds in every finite dimensional space
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Theorem 3.2, (3.15), (iv), p.14

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_PConeEB_IsNontrivialFace
import Definitions.Def_PConeEB_affineSet
import Definitions.Def_PConeEB_hyperplane
import Definitions.Def_PConeEB_IsPPS
import Definitions.Def_PConeEB_IsPosRescaledShift
import Definitions.Def_PConeEB_kappaZ
import Definitions.Def_PConeEB_lemma23FRF
import Definitions.Def_PConeEB_SatisfiesSH
import Definitions.Def_PConeEB_SatisfiesG1
import Definitions.Def_PConeEB_IsConsistentEBF

open MoreauProx.Decomposition (IsClosedConvexCone)

namespace PConeEB

/-- Theorem 3.2 (best error bounds). Suppose (Feas) is feasible, and (i) `z ∈ K* ∩ L^⊥ ∩ {a}^⊥` with
`F := K ∩ {z}^⊥` a nontrivial exposed face and `{F, L + a}` satisfying PPS; (ii) `ψ` is the 1-FRF of
Lemma 2.3 for `g`, `κ_{z,η}` as in Theorem 2.2, with `γ_{z,η} ∈ (0, ∞]` for every `η > 0`; (iii) `g`
satisfies (SH) and (G1) holds. Then (a) there is a positively rescaled shift `ψ̂` of `ψ` such that for
every bounded `B` there is `κ_B > 0` with: `x ∈ B`, `ε ≥ 0`, `dist(x, K) ≤ ε`, `dist(x, L + a) ≤ ε`
imply `dist(x, (L + a) ∩ K) ≤ κ_B (ε + ψ̂(ε, η̃))`, where `η̃ = sup_{x∈B} ‖x‖`. (b) If moreover
`‖z‖ = 1`, `L = {z}^⊥`, `a = 0`, then for every consistent error bound function `Φ` for `K, L` and
every `η̂ > 0` there are `κ̂, s₀ > 0` with `s + ψ̂(s, η̂) ≤ κ̂ Φ(κ̂ s, η̂)` for `s ∈ [0, s₀]`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Theorem 3.2, (3.15), (iv), p.14.

**Formalization Note.** (b) is stated for every positively rescaled shift of `ψ`, which covers the
`ψ̂` of (a). `η̃` is the real `sSup (norm '' B)`, finite as `B` is bounded. `[CompleteSpace E]` is
needed by `ProperCone.innerDual` and is automatic in finite dimension. -/
theorem theorem_3_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {K : Set E} (hK : IsClosedConvexCone K)
    (L : Submodule ℝ E) (a : E) (hfeas : (affineSet L a ∩ K).Nonempty)
    {z : E} (hz : z ∈ ProperCone.innerDual K) (hzL : z ∈ Lᗮ) (hza : inner ℝ z a = 0)
    (hF : IsNontrivialFace K (K ∩ hyperplane z)) (hPPS : IsPPS (K ∩ hyperplane z) L a)
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) {g : ℝ → ℝ}
    (hgmono : MonotoneOn g (Set.Ici 0)) (hg0 : g 0 = 0)
    (hgα : ∀ t, 0 ≤ t → t ^ α ≤ g t)
    (hγ : ∀ η, 0 < η → 0 < gammaZ K z g η)
    (hSH : SatisfiesSH g)
    (hG1 : ∃ (v : E) (w : ℝ → E) (Lg : ℝ), SatisfiesG1 K z g v w Lg) :
    (∃ ψhat : ℝ → ℝ → ℝ, IsPosRescaledShift ψhat (lemma23FRF z (kappaZ K z g α) g) ∧
      ∀ B : Set E, Bornology.IsBounded B → ∃ κB : ℝ, 0 < κB ∧ ∀ x ∈ B, ∀ ε : ℝ, 0 ≤ ε →
        Metric.infDist x K ≤ ε → Metric.infDist x (affineSet L a) ≤ ε →
          Metric.infDist x (affineSet L a ∩ K) ≤
            κB * (ε + ψhat ε (sSup (norm '' B)))) ∧
    (∀ ψhat : ℝ → ℝ → ℝ, IsPosRescaledShift ψhat (lemma23FRF z (kappaZ K z g α) g) →
      ‖z‖ = 1 → (L : Set E) = hyperplane z → a = 0 →
      ∀ Φ : ℝ → ℝ → ℝ, IsConsistentEBF ![K, hyperplane z] Φ →
      ∀ ηhat : ℝ, 0 < ηhat →
        ∃ κhat : ℝ, 0 < κhat ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s ∈ Set.Icc 0 s₀,
          s + ψhat s ηhat ≤ κhat * Φ (κhat * s) ηhat) := by sorry

end PConeEB
