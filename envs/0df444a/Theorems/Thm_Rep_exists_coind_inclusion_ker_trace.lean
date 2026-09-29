-- Prove2me | Theorems.Thm_Rep_exists_coind_inclusion_ker_trace
-- name    : Rep.exists_coind_inclusion_ker_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/33c8e37d-80d2-5f7f-9b28-8f03e48bc2a3
-- title:
--   Deeper coinduction: inclusion scales the trace by [U:U']
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $U' \le U$ two finite-index subgroups of $G$; let $\varphi \in G$ and let $X$ be a $k$-linear representation of $G$. Write $Y = \mathrm{coind}_{U}^{G}\,\mathrm{res}_{U}X$ and $Y' = \mathrm{coind}_{U'}^{G}\,\mathrm{res}_{U'}X$, whose elements are realised as functions $G \to X$. Assume given $G$-maps $\iota : X \to Y$, $\tau : Y \to X$, $\iota' : X \to Y'$, $\tau' : Y' \to X$ satisfying the explicit formulas $(\iota x)(g) = \rho(g)x$ and $\tau(y) = \sum_{c \in G/U} \rho(\tilde c)\,y(\tilde c^{-1})$ (a finite sum over chosen representatives $\tilde c$), and likewise for $\iota'$, $\tau'$ with $G/U'$. Assume further given objects $K, K'$ with maps $i : K \to Y$, $E : Y \to K$, $i' : K' \to Y'$, $E' : Y' \to K'$ such that $\tau(y) = 0$ exactly when $y$ lies in the image of $i$, $\tau'(y) = 0$ exactly when $y$ lies in the image of $i'$, $i'$ is injective, and the shift formulas $i(E y)(g) = \rho(\varphi)\,y(\varphi^{-1}g) - y(g)$ and $i'(E' y)(g) = \rho(\varphi)\,y(\varphi^{-1}g) - y(g)$ hold. The conclusion asserts the existence of $G$-maps $j : Y \to Y'$ and $j_K : K \to K'$ such that $j$ is the identity on underlying functions, $(j y)(g) = y(g)$ for all $g$, and such that $i' \circ j_K = j \circ i$, $j \circ \iota = \iota'$, $i'$-compatibly $j_K \circ E = E' \circ j$ after composition, and $\tau' \circ j = (U'.\mathrm{relIndex}\ U) \cdot \tau$, where the scalar is the image in $k$ of the index $[U : U']$.
--
--   This is the cochain-level statement that passing from level $U$ to a deeper level $U'$ leaves coinduced functions, the unit and the $\varphi$-shift unchanged while multiplying the trace by the index $[U:U']$, the phenomenon behind the effect of inflation on the top cohomology of a cyclic quotient. It is used in the proof of [`groupCohomology.continuousH2MapHom_surjective_of_surjective_of_primeLocal`](thm.html#groupCohomology.continuousH2MapHom_surjective_of_surjective_of_primeLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_coind_inclusion_ker_trace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.exists_coind_inclusion_ker_trace {k G : Type u} [CommRing k] [Group G]
    (U U' : Subgroup G) [U.FiniteIndex] [U'.FiniteIndex] (hUU' : U' ≤ U) (φ : G)
    (X : Rep.{u} k G)
    (ι : X ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X)
    (ι' : X ⟶ Rep.coind U'.subtype (Rep.res U'.subtype X)) (τ' : Rep.coind U'.subtype (Rep.res U'.subtype X) ⟶ X)
    (hι : ∀ (x : X) (g : G), ((ι.hom x : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ g x)
    (hτ : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = ∑ᶠ c : G ⧸ U, X.ρ c.out ((y : G → X) (c.out)⁻¹))
    (hι' : ∀ (x : X) (g : G), ((ι'.hom x : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g = X.ρ g x)
    (hτ' : ∀ y : Rep.coind U'.subtype (Rep.res U'.subtype X), τ'.hom y = ∑ᶠ c : G ⧸ U', X.ρ c.out ((y : G → X) (c.out)⁻¹))
    {K K' : Rep.{u} k G} (i : K ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (E : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ K) (i' : K' ⟶ Rep.coind U'.subtype (Rep.res U'.subtype X)) (E' : Rep.coind U'.subtype (Rep.res U'.subtype X) ⟶ K')
    (hτi : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = 0 ↔ ∃ κ : K, i.hom κ = y)
    (hi' : Function.Injective i'.hom) (hτi' : ∀ y : Rep.coind U'.subtype (Rep.res U'.subtype X), τ'.hom y = 0 ↔ ∃ κ : K', i'.hom κ = y)
    (hE : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((i.hom (E.hom y) : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ φ ((y : G → X) (φ⁻¹ * g)) - (y : G → X) g)
    (hE' : ∀ (y : Rep.coind U'.subtype (Rep.res U'.subtype X)) (g : G), ((i'.hom (E'.hom y) : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g = X.ρ φ ((y : G → X) (φ⁻¹ * g)) - (y : G → X) g) :
    ∃ (j : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ Rep.coind U'.subtype (Rep.res U'.subtype X)) (jK : K ⟶ K'),
      (∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((j.hom y : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g = (y : G → X) g) ∧
      jK ≫ i' = i ≫ j ∧ ι ≫ j = ι' ∧ E ≫ jK = j ≫ E' ∧ j ≫ τ' = (U'.relIndex U : k) • τ := by sorry
