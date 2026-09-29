-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_mvFormalGroup_comul_eq_adicEval_of_specialFibre_coordinates
-- name    : PDivisibleGroup.exists_mvFormalGroup_comul_eq_adicEval_of_specialFibre_coordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/4dfcecb2-bd3f-584e-b750-bf180fb8a488
-- title:
--   Formal group law from coordinates on a Hopf-algebra tower
-- statement:
--   Let $\mathcal O$ be a commutative ring and $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal O$, with an $\mathcal O$-algebra structure on $\mathbb Z/p$ whose structure map has kernel the ideal $(p)\subseteq\mathcal O$, and with $\mathcal O$ complete and separated for the $(p)$-adic filtration. Let $R_0(v)$, $v\in\mathbb N$, be commutative rings carrying Hopf $\mathcal O$-algebra structures which are cocommutative and free of finite rank as $\mathcal O$-modules, and let $t_0(v)\colon R_0(v+1)\to R_0(v)$ be bialgebra homomorphisms. Let $d\in\mathbb N$ and let $x(v)\colon \mathrm{Fin}\,d\to R_0(v)$ satisfy: $t_0(v)(x(v+1)_i)=x(v)_i$; $\varepsilon(x(v)_i)=0$; $x(v)_i$ lies in the radical of $(p)\subseteq R_0(v)$; the $\mathbb Z/p$-algebra map $\mathbb Z/p[X_1,\dots,X_d]\to \mathbb Z/p\otimes_{\mathcal O}R_0(v)$, $X_i\mapsto 1\otimes x(v)_i$, is surjective for every $v$; and for every $N$ there is a $v$ for which its kernel is contained in $(X_1,\dots,X_d)^N$. The conclusion asserts the existence of $F\in$ [`MvFormalGroup d 𝓞`](def/MvFormalGroup_BasicV2.html#L15) — that is, $d$ power series $F_i$ in the variables indexed by $\mathrm{Fin}\,d\sqcup\mathrm{Fin}\,d$ over $\mathcal O$ with zero constant term, linear coefficients $\delta_{ij}$ in each of the two blocks, and satisfying the associativity identity $F(F(X,Y),Z)=F(X,F(Y,Z))$ — together with a witness that $F$ is commutative, i.e. interchanging the two blocks of variables fixes each $F_i$, and $\mathcal O$-algebra homomorphisms $\pi_v\colon \mathcal O[[X_1,\dots,X_d]]\to R_0(v)$ such that: $\pi_v(X_i)=x(v)_i$; each $\pi_v$ is surjective; $\pi_{v+1}$ followed by $t_0(v)$ equals $\pi_v$; $\pi_v(X_i)$ lies in the radical of $(p)\subseteq R_0(v)$; for every power series $G$, $\pi_v(G)$ is the $(p)$-adically convergent evaluation [`MvFormalGroup.adicEval`](def/MvFormalGroup_PointsV2.html#L20) of $G$ at the $\pi_v(X_i)$; the family $(\pi_v)_v$ is jointly injective, and every family $z_v\in R_0(v)$ compatible under the $t_0(v)$ is of the form $(\pi_v(G))_v$; $\varepsilon(\pi_v(X_i))=0$; and finally $\Delta(\pi_v(X_i))$ equals the $(p)$-adic evaluation of $F_i$ in $R_0(v)\otimes_{\mathcal O}R_0(v)$ at the coordinates $\pi_v(X_j)\otimes 1$ in the first block and $1\otimes\pi_v(X_j)$ in the second.
--
--   This is the step identifying the inverse limit of a tower of finite free cocommutative Hopf $\mathcal O$-algebras, equipped with compatible formal coordinates on its special fibre, with a power series ring whose comultiplication is given by a commutative $d$-dimensional formal group law over $\mathcal O$ — the passage from the connected component of a $p$-divisible group to a commutative formal Lie group, as in Tate's work. It is used in [`PDivisibleGroup.exists_mvFormalGroup_connectedComponent_tower_of_isLocalRing_cartierDual`](thm.html#PDivisibleGroup.exists_mvFormalGroup_connectedComponent_tower_of_isLocalRing_cartierDual).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_mvFormalGroup_comul_eq_adicEval_of_specialFibre_coordinates.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MvPowerSeries
open scoped TensorProduct

universe u v

theorem PDivisibleGroup.exists_mvFormalGroup_comul_eq_adicEval_of_specialFibre_coordinates
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, HopfAlgebra 𝓞 (R₀ v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)] [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v)
    (d : ℕ) (x : ∀ v, Fin d → R₀ v) (hxt : ∀ v i, t₀ v (x (v + 1) i) = x v i)
    (hxε : ∀ v i, Coalgebra.counit (R := 𝓞) (x v i) = 0)
    (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
    (hxsurj : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)))
    (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (ZMod p)))) ^ N) :
    ∃ (F : MvFormalGroup d 𝓞) (_ : F.IsComm) (π : ∀ v, MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R₀ v),
      (∀ v i, π v (X i) = x v i) ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v).comp (π (v + 1)) = π v) ∧
      (∀ v i, π v (X i) ∈ (Ideal.span {(p : R₀ v)}).radical) ∧
      (∀ v G, π v G = MvFormalGroup.adicEval (Ideal.span {(p : R₀ v)}) (fun i => π v (X i)) G) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, R₀ v, (∀ v, t₀ v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) ∧
      (∀ v i, Coalgebra.counit (R := 𝓞) (π v (X i)) = 0) ∧
      (∀ v i, Coalgebra.comul (R := 𝓞) (π v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : R₀ v ⊗[𝓞] R₀ v)})
          (Sum.elim (fun j => π v (X j) ⊗ₜ[𝓞] (1 : R₀ v)) (fun j => (1 : R₀ v) ⊗ₜ[𝓞] π v (X j)))
          (F.toPowerSeries i)) := by sorry
