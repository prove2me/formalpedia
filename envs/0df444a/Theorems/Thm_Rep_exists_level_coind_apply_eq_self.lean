-- Prove2me | Theorems.Thm_Rep_exists_level_coind_apply_eq_self
-- name    : Rep.exists_level_coind_apply_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/298fa081-0555-503d-8114-324106b09738
-- title:
--   Coinduction preserves level-smoothness along a finite-index subgroup
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $r \colon G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be a group homomorphism into the group of $\mathbb{Q}$-algebra automorphisms of an algebraic closure of $\mathbb{Q}$. Let $S \le G$ be a subgroup of finite index, and assume that $S$ is open for the level topology induced by $r$, in the sense that there is an intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, whose pointwise fixing subgroup has preimage under $r$ contained in $S$. Let $N$ be a $k$-linear representation of $S$ which is smooth for the restriction of $r$ to $S$: for every vector $n \in N$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $s \in S$ with $r(s)$ fixing $F$ pointwise satisfies $\rho_N(s)\,n = n$. Then for every element $f$ of the coinduced representation $\mathrm{coind}_{S}^{G} N$ of $G$ along the inclusion $S \hookrightarrow G$ — the space of functions $f \colon G \to N$ with $f(s x) = \rho_N(s) f(x)$, with $G$ acting by $(\rho(u) f)(x) = f(x u)$ — there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that $\rho(u) f = f$ for every $u \in G$ with $r(u)$ fixing $F$ pointwise. That is, each vector of the coinduced representation is level-smooth for $r$.
--
--   This is the smoothness input for the continuous version of Shapiro's lemma in the level-topology setting: coinduction from an open finite-index subgroup carries smooth representations to smooth representations. It is used by [`Rep.exists_shortExact_coind_res`](thm.html#Rep.exists_shortExact_coind_res) and by the bijectivity statements [`groupCohomology.bijective_theta_coind`](thm.html#groupCohomology.bijective_theta_coind) and [`groupCohomology.bijective_theta_dualTwist_of_res`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res) for the comparison maps between continuous and abstract group cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_level_coind_apply_eq_self.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.exists_level_coind_apply_eq_self {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G) [S.FiniteIndex]
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, r s ∈ F.fixingSubgroup → N.ρ s n = n)
    (f : Rep.coind S.subtype N) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ u : G, r u ∈ F.fixingSubgroup → (Rep.coind S.subtype N).ρ u f = f := by sorry
