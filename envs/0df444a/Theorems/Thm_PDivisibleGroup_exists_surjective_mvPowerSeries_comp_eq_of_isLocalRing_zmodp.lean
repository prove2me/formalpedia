-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_surjective_mvPowerSeries_comp_eq_of_isLocalRing_zmodp
-- name    : PDivisibleGroup.exists_surjective_mvPowerSeries_comp_eq_of_isLocalRing_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/33937e94-3fe2-5b7c-aff2-5530a61b1e18
-- title:
--   Power-series coordinates on a connected p-divisible tower over 𝔽ₚ
-- statement:
--   Fix a prime $p$ and a natural number $h_0$, and let $H$ be a family of commutative rings $H(v)$, $v \in \mathbb{N}$, each carrying a Hopf algebra structure over $\mathbb{Z}/p$ whose comultiplication is cocommutative and which is finite as a $\mathbb{Z}/p$-module. Let $s(v) \colon H(v+1) \to H(v)$ be $\mathbb{Z}/p$-bialgebra maps that are surjective, with $\operatorname{finrank}_{\mathbb{Z}/p} H(v) = p^{v h_0}$ and with $\ker s(v)$ equal to the $p^v$-torsion ideal of $H(v+1)$, i.e. the image of the augmentation ideal (the kernel of the counit, viewed as an algebra map) under the algebra endomorphism given by the $p^v$-th convolution power of the identity; assume further that each $H(v)$ is a local ring. Then there exist a natural number $d$ and $\mathbb{Z}/p$-algebra maps $\pi_v \colon (\mathbb{Z}/p)[[X_1,\dots,X_d]] \to H(v)$ such that: $d$ is the $\mathbb{Z}/p$-dimension of the cotangent module $I/I^2$ of the augmentation ideal $I$ of $H(1)$; each $\pi_v$ is surjective; $\pi_{v+1}$ followed by $s(v)$ equals $\pi_v$; each $\pi_v(X_i)$ has counit $0$ and is nilpotent; for every $N$ there is a $v$ with $\ker \pi_v \subseteq (X_1,\dots,X_d)^N$; the $\pi_v$ are jointly injective; and every family $(z_v)$ with $s(v)(z_{v+1}) = z_v$ is of the form $(\pi_v(G))_v$ for some power series $G$.
--
--   This is the field case of the statement that the coordinate rings of a connected $p$-divisible group over $\mathbb{F}_p$ assemble into a power series ring, $\varprojlim_v \mathcal{O}(G_v) \cong \mathbb{F}_p[[X_1,\dots,X_d]]$ with $d$ the cotangent dimension, the last two clauses expressing precisely that $(\pi_v)$ induces an isomorphism onto the inverse limit. It supplies the coordinates used to equip such a tower with a multivariate formal group law whose kernel ideals are described by the transition maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_surjective_mvPowerSeries_comp_eq_of_isLocalRing_zmodp.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MvPowerSeries

universe v

theorem PDivisibleGroup.exists_surjective_mvPowerSeries_comp_eq_of_isLocalRing_zmodp
    (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Function.Surjective (s v))
    (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
    (hkerH : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
    (hlocH : ∀ v, IsLocalRing (H v)) :
    ∃ (d : ℕ) (π : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] H v),
      d = Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H 1)).Cotangent ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (s v : H (v + 1) →ₐ[ZMod p] H v).comp (π (v + 1)) = π v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (π v (X i)) = 0) ∧
      (∀ v i, IsNilpotent (π v (X i))) ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (π v) ≤
        (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, H v, (∀ v, s v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) := by sorry
