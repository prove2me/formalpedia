-- Prove2me | Theorems.Thm_PDivisibleGroup_Tower_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
-- name    : PDivisibleGroup.Tower.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/8b0e7cae-40cb-5c98-9cea-77f13d73cda5
-- title:
--   Tate's sequence 0→ Gᵤ→ Gᵥ₊ᵤ→ Gᵥ→ 0 for towers
-- statement:
--   Let $R$ be a commutative ring and let $p,h$ be natural numbers (no primality is assumed). Let $L\colon\mathbb{N}\to\mathrm{Type}$ be a family of commutative rings, each carrying a Hopf $R$-algebra structure whose comultiplication is cocommutative and which is free and finite as an $R$-module; let $t_w\colon L(w+1)\to L(w)$ be $R$-bialgebra homomorphisms, each surjective, with $\operatorname{finrank}_R L(w)=p^{wh}$ for all $w$, and with $\ker t_w$ equal to the ideal of $L(w+1)$ obtained by pushing the augmentation ideal $\ker(\varepsilon)$ forward along [`PDivisibleGroup.Hopf.nsmulAlgHom R (L (w+1)) (p^w)`](def/PDivisibleGroup_Basic.html#L16), the $p^w$-th convolution power of the identity. Fix $v,u\in\mathbb{N}$ and write $C$ for the range of $\varphi:=$ `nsmulAlgHom R (L (v+u)) (p^u)`, an $R$-subalgebra of $L(v+u)$. The assertion is fivefold: there is an $R$-algebra isomorphism $e\colon L(v)\xrightarrow{\sim} C$ with $e(\,\mathrm{transitionLE}\,t\,v\,u\,(a))=\varphi(a)$ in $L(v+u)$ for every $a\in L(v+u)$, where $\mathrm{transitionLE}\,t\,v\,u$ is the composite $t_v\circ\cdots\circ t_{v+u-1}$ defined by recursion on $u$; $L(v+u)$ is finite and projective as a $C$-module; there is a $C$-linear map $r\colon L(v+u)\to C$ restricting to the identity on $C$; and for every prime $\mathfrak{q}$ of $C$ the rank of $L(v+u)$ at the stalk $\mathfrak{q}$ equals $p^{uh}$.
--
--   In the geometric language this is Tate's iterated exact sequence $0\to G_u\to G_{v+u}\to G_v\to 0$ for a $p$-divisible group presented by an explicit tower of level Hopf algebras: multiplication by $p^u$ on $G_{v+u}$ factors through the closed immersion $G_v\hookrightarrow G_{v+u}$, identifying $G_v$ with the scheme-theoretic quotient $G_{v+u}/G_u$, and the resulting map is finite locally free of constant degree $p^{uh}$ with a direct summand splitting of the structure map. It feeds the analysis of towers over coefficient rings used later, being cited by [`PDivisibleGroup.Tower.surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp`](thm.html#PDivisibleGroup.Tower.surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_Tower_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem PDivisibleGroup.Tower.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
    {R : Type u} [CommRing R] (p h : ℕ)
    (L : ℕ → Type v) [∀ w, CommRing (L w)] [∀ w, HopfAlgebra R (L w)]
    [∀ w, Coalgebra.IsCocomm R (L w)] [∀ w, Module.Free R (L w)] [∀ w, Module.Finite R (L w)]
    (t : ∀ w, L (w + 1) →ₐc[R] L w) (ht : ∀ w, Function.Surjective (t w))
    (hrankL : ∀ w, Module.finrank R (L w) = p ^ (w * h))
    (hkerL : ∀ w, RingHom.ker (t w) = PDivisibleGroup.Hopf.torsionIdeal R (L (w + 1)) (p ^ w))
    (v u : ℕ) :
    (∃ e : L v ≃ₐ[R] ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
        ∀ a : L (v + u),
          ((e (PDivisibleGroup.Tower.transitionLE t v u a) :
              ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range) : L (v + u)) =
            PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u) a) ∧
      Module.Finite ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range (L (v + u)) ∧
      Module.Projective ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range (L (v + u)) ∧
      (∃ r : L (v + u) →ₗ[↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range]
          ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
        ∀ c : ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
          r (c : L (v + u)) = c) ∧
      ∀ 𝔮 : PrimeSpectrum ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
        Module.rankAtStalk (R := ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range)
          (L (v + u)) 𝔮 = p ^ (u * h) := by sorry
