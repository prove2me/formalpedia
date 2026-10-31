-- Prove2me | Theorems.Thm_PopularMixed_mixed_fractional_bridge
-- name    : PopularMixed.mixed_fractional_bridge
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:55:54.283071+00:00
-- url     : https://prove2.me/theorems/2430ef56-1d9d-4221-9be6-fcfe3e237c1b
-- title:
--   Section 2 (after (2.1)) — mixed matchings and fractional matchings: $\Delta(\vec x,M)=\Delta(\Pi,M)$
-- statement:
--   Let $G=(A\cup B,E)$ be an instance with strict preference lists. For a mixed matching $\Lambda$ write $x_\Lambda=\sum_M\Lambda(M)\,I_M$.
--
--   1. For every mixed matching $\Lambda$: $\Delta(\Lambda,M')=\Delta(x_\Lambda,M')$ for every matching $M'$; hence $\Lambda$ is popular (Definition 2) if and only if $x_\Lambda\in\mathcal P_G$; and its utility is $\sum_{(a,b)}w(a,b)\,x_\Lambda(a,b)$ for every $w$.
--   2. Every fractional matching $\vec x\in\mathcal M_G$ is $x_\Lambda$ for some mixed matching $\Lambda$ ("in a bipartite graph, a fractional matching is equivalent to a mixed matching").
--   3. Every half-integral fractional matching $\vec q$ of $G$ is $x_\Pi$ for $\Pi=\{(M_0,\tfrac12),(M_1,\tfrac12)\}$, i.e.
--   $$\vec q=\tfrac12 I_{M_0}+\tfrac12 I_{M_1}$$
--   for some matchings $M_0,M_1$ of $G$ — every vertex "has at most two partners and spends the same amount of time with each".
--
--   These facts carry the polyhedral results on $\mathcal P_G$ over to popular mixed matchings in Theorem 1.1.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - encoding: mixed matching {(M_0,p_0),…,(M_k,p_k)}, p_i ≥ 0, Σ p_i = 1 → Λ : Finset (A × B) → ℝ, Λ ≥ 0, Σ_M Λ M = 1, Λ M ≠ 0 only for matchings M; reason: repeated matchings are merged; every finite lottery over matchings is such a Λ and conversely
--   - reading: "Δ(x,M) = Δ(Π,M) and Π is a mixed matching corresponding to the fractional matching x (recall that in a bipartite graph, a fractional matching is equivalent to a mixed matching)"; "every vertex has at most two partners and spends the same amount of time with each" → three conjuncts: Δ(Λ,M′) = Δ(x_Λ,M′), popularity and utility transfer for mixed Λ; every x ∈ M_G is some x_Λ; every half-integral q ∈ M_G is x_{half M₀ M₁}; reason: the correspondence Π ↔ x is stated in both directions; (3) is the structure claimed on PDF p.2 for the half-integral optimum
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Section 2, PDF p.4 (after (2.1)); Section 1, PDF p.2 (Birkhoff–von Neumann remark; the paragraph after Theorem 1.1).

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), PDF p.4 after (2.1) and
PDF p.2: (i) "`Δ(x, M) = Δ(Π, M)` and `Π` is a mixed matching corresponding to the fractional
matching `x`", so a mixed matching `Λ` is popular (Definition 2) iff its fractional matching
`x_Λ = Σ_M Λ(M) I_M` lies in `P_G`, and the utility of `Λ` is `Σ_{(a,b)} w(a,b) x_Λ(a,b)`;
(ii) conversely every fractional matching `x ∈ M_G` is `x_Λ` for a mixed matching `Λ` ("in a
bipartite graph, a fractional matching is equivalent to a mixed matching", PDF p.4; the
Birkhoff–von Neumann theorem, PDF p.2); (iii) every half-integral fractional matching `q` of the bipartite graph `G` is
`{(M₀, 1/2), (M₁, 1/2)}`, i.e. `q = ½ I_{M₀} + ½ I_{M₁}` for matchings `M₀, M₁` of `G` ("every
vertex has at most two partners and spends the same amount of time with each", PDF p.2). -/
theorem mixed_fractional_bridge {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    (∀ Λ : Finset (A × B) → ℝ, G.IsMixed Λ →
      (∀ M', G.IsMatching M' → G.deltaMixed Λ M' = G.deltaFrac (mixedToFrac Λ) M') ∧
      (G.IsPopularMixed Λ ↔ G.InPG (mixedToFrac Λ)) ∧
      ∀ w : A → B → ℝ, utility w Λ = ∑ a, ∑ b, w a b * mixedToFrac Λ a b) ∧
    (∀ x : A → B → ℝ, G.InMG x → ∃ Λ, G.IsMixed Λ ∧ mixedToFrac Λ = x) ∧
    ∀ q : A → B → ℝ, G.InMG q → IsHalfIntegral q →
      ∃ M₀ M₁, G.IsMatching M₀ ∧ G.IsMatching M₁ ∧ q = mixedToFrac (half M₀ M₁) := by sorry

end PopularMixed
