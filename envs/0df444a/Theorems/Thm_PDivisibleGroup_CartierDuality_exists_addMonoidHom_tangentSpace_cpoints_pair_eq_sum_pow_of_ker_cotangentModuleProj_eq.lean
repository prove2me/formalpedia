-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq
-- name    : PDivisibleGroup.CartierDuality.exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/27e69f25-2e29-5ffd-9793-b8e328756e03
-- title:
--   Exponential of a p-divisible group and the Cartier pairing
-- statement:
--   Let $p$ be a prime and let $R$ be a commutative $\mathbb{Z}_p$-algebra in which $p$ is not a zero divisor ($px=0$ forces $x=0$) and which is $p$-adically separated (if $x$ lies in $p^iR$ for every $i$ then $x=0$). Let $G,G'$ be $p$-divisible groups of height $h$ over $R$, each given by a tower of finite free commutative cocommutative Hopf $R$-algebras $G.\mathrm{level}\,v$ of rank $p^{vh}$ with surjective transition maps whose kernels are the $p^v$-torsion ideals, and let $D$ be a Cartier duality datum between them, i.e. coalgebra-algebra isomorphisms $G'.\mathrm{level}\,v \simeq \mathrm{CartierDual}_R(G.\mathrm{level}\,v)$ compatible with the transitions and multiplication by $p$. Assume that for every $v$ the projection $\omega_G = G.\mathrm{cotangentModule} \to G.\mathrm{Cotangent}\,v$ is surjective with kernel $p^v\omega_G$. Then there are a natural number $m$, a family $c : \mathbb{N} \to R$ with $k!\,c_k = p^{mk}$ for all $k$, and an injective additive map $e$ from the tangent space $t_G(R)=\operatorname{Hom}_R(\omega_G,R)$ to the completed points $G(R)^\wedge = \varprojlim_i G(R/p^iR)$, such that for every commutative $R$-algebra $S$, every $\tau \in t_G(R)$, all $i \le w$, every $f : G.\mathrm{Point}\,(S/p^iS)\,w$ whose image in $G(S/p^iS)$ is the $i$-th component of the image of $e(\tau)$ under the structural map $R \to S$, every $\psi : G'.\mathrm{Point}\,S\,w$ and every $z \in S \otimes_R \omega_G$ lifting the character differential $D.\mathrm{charDiff}\,S\,w\,\psi \in S \otimes_R G.\mathrm{Cotangent}\,w$ along the projection, the Cartier pairing of $f$ with the reduction of $\psi$ modulo $p^i$ equals $\sum_{k<i} c_k\,\bar{u}^{\,k}$ in $S/p^iS$, where $u \in S$ is the image of $z$ under $\tau$ tensored with $S$ (identifying $S \otimes_R R$ with $S$) and $\bar u$ its class modulo $p^i$.
--
--   This is the analytic input of Tate's proof that the period map of a $p$-divisible group is injective: the exponential of the formal group, convergent on $p^m$ times the integral tangent space, together with the compatibility $\langle \exp(p^m\tau), \psi\rangle = \sum_{k} (p^{mk}/k!)\,\langle \tau, d\chi_\psi\rangle^k$ between the Cartier pairing and the differential of the character attached to $\psi$. It is used in the proof of linear independence of the Tate module inside the $p$-adic completion, [`PDivisibleGroup.CartierDuality.linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers`](thm.html#PDivisibleGroup.CartierDuality.linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import Definitions.Def_PDivisibleGroup_CompletedPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct in

theorem PDivisibleGroup.CartierDuality.exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra ℤ_[p] R]
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ i : ℕ, x ∈ Ideal.span {(p : R) ^ i}) → x = 0)
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (hsurj : ∀ v, Function.Surjective (G.cotangentModuleProj v))
    (hker : ∀ v, LinearMap.ker (G.cotangentModuleProj v) =
      Ideal.span {(p : R) ^ v} • (⊤ : Submodule R G.cotangentModule)) :
    ∃ (m : ℕ) (c : ℕ → R) (e : G.tangentSpace R →+ G.CPoints R),
      (∀ k : ℕ, (k.factorial : R) * c k = (p : R) ^ (m * k)) ∧
      Function.Injective e ∧
      ∀ (S : Type) [CommRing S] [Algebra R S] (τ : G.tangentSpace R) (i w : ℕ), i ≤ w →
        ∀ (f : G.Point (S ⧸ Ideal.span {(p : S) ^ i}) w),
          G.pointsMkAdd _ w (Additive.ofMul f) =
            G.cpointsProj S i (G.cpointsMap (Algebra.ofId R S) (e τ)) →
        ∀ (ψ : G'.Point S w) (z : S ⊗[R] G.cotangentModule),
          (G.cotangentModuleProj w).lTensor S z = D.charDiff S w ψ →
          D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})) w ψ) =
            ∑ k ∈ Finset.range i,
              algebraMap R _ (c k) *
                (Ideal.Quotient.mk (Ideal.span {(p : S) ^ i})
                  (TensorProduct.rid R S (τ.lTensor S z))) ^ k := by sorry
