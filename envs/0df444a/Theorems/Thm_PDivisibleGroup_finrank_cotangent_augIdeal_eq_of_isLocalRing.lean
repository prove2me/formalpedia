-- Prove2me | Theorems.Thm_PDivisibleGroup_finrank_cotangent_augIdeal_eq_of_isLocalRing
-- name    : PDivisibleGroup.finrank_cotangent_augIdeal_eq_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/4da68bc1-58e1-53ca-828a-917bc8e46076
-- title:
--   Constancy of the cotangent dimension along the levels
-- statement:
--   Let $p$ be a prime, let $h_0$ be a natural number, and let $H : \mathbb{N} \to \mathrm{Type}$ be a family of commutative rings, each carrying a Hopf algebra structure over $\mathbb{Z}/p$ with cocommutative comultiplication and finite as a $\mathbb{Z}/p$-module. Suppose given, for each $v$, a bialgebra (algebra and coalgebra) homomorphism $s_v : H(v+1) \to H(v)$ over $\mathbb{Z}/p$, and assume: each $s_v$ is surjective; $\dim_{\mathbb{Z}/p} H(v) = p^{v h_0}$ for all $v$; the kernel of $s_v$ equals [`PDivisibleGroup.Hopf.torsionIdeal`](def/PDivisibleGroup_Basic.html#L157) of $H(v+1)$ at $p^{v}$, that is, the image of the augmentation ideal $I_{v+1} = \ker(\varepsilon_{H(v+1)})$ under the algebra endomorphism `nsmulAlgHom` attached to $p^{v}$ (the $p^{v}$-th convolution power of the identity, i.e. the comorphism of multiplication by $p^{v}$); and each $H(v)$ is a local ring. Then for every $w \ge 1$ one has $\dim_{\mathbb{Z}/p} \bigl(I_w/I_w^2\bigr) = \dim_{\mathbb{Z}/p}\bigl(I_1/I_1^2\bigr)$, where $I_w = \ker(\varepsilon_{H(w)})$ and $I_w/I_w^2$ is its cotangent module.
--
--   For a $p$-divisible group over $\mathbb{F}_p$ presented as a tower of finite Hopf algebras, this is the statement that the cotangent space at the origin of the level $w$ has dimension independent of $w \ge 1$, the classical reason being that $p$ annihilates the Lie algebra in characteristic $p$, so that $\Gamma_w[p] = \Gamma_1$ has the same Lie algebra as $\Gamma_w$. It feeds into [`PDivisibleGroup.finrank_quotient_span_pow_augIdeal_eq_pow_of_isLocalRing`](thm.html#PDivisibleGroup.finrank_quotient_span_pow_augIdeal_eq_pow_of_isLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_finrank_cotangent_augIdeal_eq_of_isLocalRing.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe v

theorem PDivisibleGroup.finrank_cotangent_augIdeal_eq_of_isLocalRing
    (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Function.Surjective (s v))
    (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
    (hkerH : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
    (hlocH : ∀ v, IsLocalRing (H v))
    (w : ℕ) (hw : 1 ≤ w) :
    Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w)).Cotangent =
      Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H 1)).Cotangent := by sorry
