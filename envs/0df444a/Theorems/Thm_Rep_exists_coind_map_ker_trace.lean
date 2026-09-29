-- Prove2me | Theorems.Thm_Rep_exists_coind_map_ker_trace
-- name    : Rep.exists_coind_map_ker_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/8f948e6b-e25f-5a40-801f-02dc54b03df2
-- title:
--   Functoriality of coinduction, unit, shift and trace
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $U \le G$ a subgroup of finite index, and $\varphi \in G$. For a $k$-linear representation $X$ of $G$ write $Y_X =$ `Rep.coind U.subtype (Rep.res U.subtype X)` for the coinduction along $U \hookrightarrow G$ of the restriction of $X$, whose elements are coerced to functions $G \to X$. Given representations $X, X'$, a morphism $f : X \to X'$, morphisms $\iota : X \to Y_X$, $\tau : Y_X \to X$, $\iota' : X' \to Y_{X'}$, $\tau' : Y_{X'} \to X'$ subject to $\iota(x)(g) = X.\rho(g)x$ and $\tau(y) = \sum^{\mathrm f}_{c \in G/U} X.\rho(\bar c)\,y(\bar c^{-1})$ (the finite sum over chosen representatives $\bar c$ of the cosets), and likewise for $\iota', \tau'$; and given representations $K, K'$ with morphisms $i : K \to Y_X$, $E : Y_X \to K$, $i' : K' \to Y_{X'}$, $E' : Y_{X'} \to K'$ such that $i'$ is injective, the image of $i$ is exactly the kernel of $\tau$, the image of $i'$ is exactly the kernel of $\tau'$, and $i(E(y))(g) = X.\rho(\varphi)\,y(\varphi^{-1}g) - y(g)$, with the same formula for $i' \circ E'$ over $X'$. Then there exist morphisms $Y_f : Y_X \to Y_{X'}$ and $K_f : K \to K'$ with $(Y_f y)(g) = f(y(g))$ for all $y$ and $g \in G$, and with $i' \circ K_f = Y_f \circ i$, $Y_f \circ \iota = \iota' \circ f$, $K_f \circ E = E' \circ Y_f$ and $f \circ \tau = \tau' \circ Y_f$.
--
--   This is the functoriality in $X$ of coinduction from a finite-index subgroup together with the unit, the shift by $\varphi$ and the trace, i.e. of the four-term complex $0 \to X \to Y_X \to Y_X \to X \to 0$ obtained from the periodic resolution of a finite cyclic quotient $G/U$; the data $(\iota, \tau, i, E)$ are supplied axiomatically by the displayed formulas rather than constructed. It is used in the proof that the map induced on (continuous) $H^2$ is surjective for surjections in the prime-local situation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_coind_map_ker_trace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory

theorem Rep.exists_coind_map_ker_trace {k G : Type u} [CommRing k] [Group G]
    (U : Subgroup G) [U.FiniteIndex] (φ : G)
    {X X' : Rep.{u} k G} (f : X ⟶ X')
    (ι : X ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X)
    (ι' : X' ⟶ Rep.coind U.subtype (Rep.res U.subtype X')) (τ' : Rep.coind U.subtype (Rep.res U.subtype X') ⟶ X')
    (hι : ∀ (x : X) (g : G), ((ι.hom x : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ g x)
    (hτ : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = ∑ᶠ c : G ⧸ U, X.ρ c.out ((y : G → X) (c.out)⁻¹))
    (hι' : ∀ (x : X') (g : G), ((ι'.hom x : Rep.coind U.subtype (Rep.res U.subtype X')) : G → X') g = X'.ρ g x)
    (hτ' : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X'), τ'.hom y = ∑ᶠ c : G ⧸ U, X'.ρ c.out ((y : G → X') (c.out)⁻¹))
    {K K' : Rep.{u} k G} (i : K ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (E : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ K) (i' : K' ⟶ Rep.coind U.subtype (Rep.res U.subtype X')) (E' : Rep.coind U.subtype (Rep.res U.subtype X') ⟶ K')
    (hi' : Function.Injective i'.hom) (hτi' : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X'), τ'.hom y = 0 ↔ ∃ κ : K', i'.hom κ = y)
    (hE : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((i.hom (E.hom y) : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ φ ((y : G → X) (φ⁻¹ * g)) - (y : G → X) g)
    (hE' : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype X')) (g : G), ((i'.hom (E'.hom y) : Rep.coind U.subtype (Rep.res U.subtype X')) : G → X') g = X'.ρ φ ((y : G → X') (φ⁻¹ * g)) - (y : G → X') g)
    (hτi : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = 0 ↔ ∃ κ : K, i.hom κ = y) :
    ∃ (Yf : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ Rep.coind U.subtype (Rep.res U.subtype X')) (Kf : K ⟶ K'),
      (∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((Yf.hom y : Rep.coind U.subtype (Rep.res U.subtype X')) : G → X') g = f.hom ((y : G → X) g)) ∧
      Kf ≫ i' = i ≫ Yf ∧ ι ≫ Yf = f ≫ ι' ∧ E ≫ Kf = Yf ≫ E' ∧ τ ≫ f = Yf ≫ τ' := by sorry
