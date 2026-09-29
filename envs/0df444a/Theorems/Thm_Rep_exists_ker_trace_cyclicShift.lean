-- Prove2me | Theorems.Thm_Rep_exists_ker_trace_cyclicShift
-- name    : Rep.exists_ker_trace_cyclicShift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/3d4ff18d-e7c6-5522-8a78-3876d1acc54a
-- title:
--   Shift-minus-one operator on CoInd_U^GRes_U X
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $U\trianglelefteq G$ a normal subgroup of finite index, and let $\varphi\in G$ be an element such that every $g\in G$ can be written $g=\varphi^{n}u$ with $n\in\mathbb{Z}$ and $u\in U$ (so the image of $\varphi$ generates the finite group $G/U$). Let $X$ be a $k$-linear representation of $G$ and put $Y=\mathrm{Rep.coind}\,U.\mathrm{subtype}\,(\mathrm{Rep.res}\,U.\mathrm{subtype}\,X)$, the representation coinduced along $U\hookrightarrow G$ from the restriction of $X$. Assume given morphisms $\iota:X\to Y$ and $\tau:Y\to X$ of representations such that $\iota(x)$ is the function $g\mapsto \rho_X(g)x$, and such that $\tau(f)=\sum_{c\in G/U}\rho_X(\tilde c)\,f(\tilde c^{-1})$, the finite sum over $G/U$ of values at the inverses of chosen representatives $\tilde c$. The assertion is the existence of a representation $K$ and morphisms $i:K\to Y$, $E:Y\to K$ such that: $i$ is injective on underlying elements; for $f\in Y$ one has $\tau(f)=0$ if and only if $f$ lies in the image of $i$; for all $f\in Y$ and $g\in G$, $i(E(f))(g)=\rho_X(\varphi)\bigl(f(\varphi^{-1}g)\bigr)-f(g)$; $\iota$ is injective; $E$ is surjective; and $E(f)=0$ if and only if $f$ lies in the image of $\iota$.
--
--   This packages the four-term exact sequence $0\to X\to Y\xrightarrow{\bar\varphi-1}Y\to X\to 0$ attached to the periodic free resolution of the finite cyclic group $G/U=\langle\bar\varphi\rangle$, written on the coinduced representation: the shift-minus-one operator factors as a surjection $E$ onto a representation $K$ followed by an injection $i$ with image the kernel of the trace, while the kernel of $E$ is the image of the unit $\iota$. It is used in the surjectivity statement for the map induced on continuous $H^2$ by a surjection of coefficients in the prime-local setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_ker_trace_cyclicShift.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.exists_ker_trace_cyclicShift {k G : Type u} [CommRing k] [Group G]
    (U : Subgroup G) [U.Normal] [U.FiniteIndex] (φ : G) (hφ : ∀ g : G, ∃ (n : ℤ) (u : G), u ∈ U ∧ g = φ ^ n * u)
    (X : Rep.{u} k G)
    (ι : X ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X)
    (hι : ∀ (x : X) (g : G), ((ι.hom x : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ g x)
    (hτ : ∀ f : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom f = ∑ᶠ c : G ⧸ U, X.ρ c.out ((f : G → X) (c.out)⁻¹)) :
    ∃ (K : Rep.{u} k G) (i : K ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (E : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ K),
      Function.Injective i.hom ∧
      (∀ f : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom f = 0 ↔ ∃ κ : K, i.hom κ = f) ∧
      (∀ (f : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G),
        ((i.hom (E.hom f) : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ φ ((f : G → X) (φ⁻¹ * g)) - (f : G → X) g) ∧
      Function.Injective ι.hom ∧ Function.Surjective E.hom ∧
      (∀ f : Rep.coind U.subtype (Rep.res U.subtype X), E.hom f = 0 ↔ ∃ x : X, ι.hom x = f) := by sorry
