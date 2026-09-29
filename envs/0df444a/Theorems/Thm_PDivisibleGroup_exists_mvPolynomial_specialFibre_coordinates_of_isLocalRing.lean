-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_mvPolynomial_specialFibre_coordinates_of_isLocalRing
-- name    : PDivisibleGroup.exists_mvPolynomial_specialFibre_coordinates_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/4eb042aa-2d23-52e1-b4a8-8cbb378c6eb3
-- title:
--   Polynomial coordinates on the special fibre of a connected p-divisible group
-- statement:
--   Let $p$ be a prime and let $\mathcal O$ be a commutative ring in which $p$ is a non-zero-divisor, equipped with an $\mathcal O$-algebra structure on $\mathbb Z/p$ whose structure map has kernel the ideal $(p)$, and which is complete and separated for the $(p)$-adic topology. Let $h_0$ be a natural number and let $(R_0(v))_{v\ge 0}$ be a family of commutative rings, each a cocommutative Hopf $\mathcal O$-algebra that is finite and free as an $\mathcal O$-module, together with bialgebra maps $t_0(v)\colon R_0(v+1)\to R_0(v)$ that are surjective, such that $\operatorname{rank}_{\mathcal O}R_0(v)=p^{vh_0}$, such that $\ker t_0(v)$ is the $p^v$-torsion ideal of $R_0(v+1)$, i.e. the image of the augmentation ideal (the kernel of the counit) under the algebra endomorphism given by the $p^v$-fold convolution power of the identity, and such that each $R_0(v)$ is a local ring. Then there exist $d\in\mathbb N$ and $\mathbb Z/p$-algebra homomorphisms $\bar\pi_v\colon (\mathbb Z/p)[X_1,\dots,X_d]\to \mathbb Z/p\otimes_{\mathcal O}R_0(v)$ for all $v$ such that: each $\bar\pi_v$ is surjective; $\bar\pi_{v+1}$ followed by the base change $\mathrm{id}\otimes t_0(v)$ equals $\bar\pi_v$; the counit of $\mathbb Z/p\otimes_{\mathcal O}R_0(v)$ kills each $\bar\pi_v(X_i)$; and for every $N$ there is a $v$ with $\ker\bar\pi_v\subseteq (X_1,\dots,X_d)^N$.
--
--   This is the special-fibre half of Tate's theorem that a connected $p$-divisible group over a $p$-adically complete base with residue field $\mathbb F_p$ is a formal Lie group: the levels of the reduction mod $p$ are uniformised by compatible surjections from a polynomial ring in $d$ variables, $d$ being the dimension, with kernels shrinking $(X)$-adically, so that the inverse limit is $\mathbb F_p[[X_1,\dots,X_d]]$. It feeds [`PDivisibleGroup.exists_compatible_specialFibre_coordinates_of_isLocalRing`](thm.html#PDivisibleGroup.exists_compatible_specialFibre_coordinates_of_isLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_mvPolynomial_specialFibre_coordinates_of_isLocalRing.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem PDivisibleGroup.exists_mvPolynomial_specialFibre_coordinates_of_isLocalRing
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h₀ : ℕ) (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, HopfAlgebra 𝓞 (R₀ v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)] [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v) (ht₀ : ∀ v, Function.Surjective (t₀ v))
    (hrank₀ : ∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀))
    (hker₀ : ∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (R₀ v)) :
    ∃ (d : ℕ) (πbar : ∀ v, MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)),
      (∀ v, Function.Surjective (πbar v)) ∧
      (∀ v, (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)).comp
        (πbar (v + 1)) = πbar v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (A := TensorProduct 𝓞 (ZMod p) (R₀ v))
        (πbar v (MvPolynomial.X i)) = 0) ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (πbar v) ≤
        (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (ZMod p)))) ^ N) := by sorry
