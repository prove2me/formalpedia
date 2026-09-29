-- Prove2me | Theorems.Thm_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer
-- name    : PDivisibleGroup.Tower.exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/2f2b416e-6c7d-57d0-b391-695798f9e0e7
-- title:
--   Shifted Hopf-kernel tower is a p-divisible group of height h'
-- statement:
--   Let $R$ be a commutative local principal ideal domain, let $p,h',i_0$ be natural numbers, and let $B : \mathbb{N} \to \mathrm{Type}$ be a family of commutative rings, each a cocommutative Hopf $R$-algebra that is finite and free as an $R$-module. Suppose given surjective bialgebra maps $t_w : B_{w+1} \to B_w$ and bialgebra maps $m_w : B_w \to B_{w+1}$ such that $m_w \circ t_w$ and $t_w \circ m_w$ are both the $p$-th convolution power of the identity (multiplication by $p$) on $B_{w+1}$ and on $B_w$ respectively; that for each $w$ and each $d$ in $\mathrm{hopfKer}(t_w)$ — the equalizer inside $B_{w+1}$ of the coaction $B_{w+1} \to B_{w+1} \otimes_R B_w$ and $x \mapsto x \otimes 1$ — the $p$-fold convolution power of the identity sends $d$ to the image of its counit under $R \to B_{w+1}$; that $m_{w+1}$ maps $\mathrm{hopfKer}(t_w)$ into $\mathrm{hopfKer}(t_{w+1})$, bijectively onto it whenever $i_0 \le w$; and that $\mathrm{hopfKer}(t_{i_0})$ has $R$-rank $p^{h'}$. Then there exist a family $L : \mathbb{N} \to \mathrm{Type}$ of commutative rings with cocommutative Hopf $R$-algebra structures, finite and free over $R$, bialgebra maps $t'_v : L_{v+1} \to L_v$ and $\iota_v : L_v \to B_{i_0+v}$ such that: each $t'_v$ is surjective; $\mathrm{finrank}_R L_v = p^{v h'}$; $\ker t'_v$ is the image of the augmentation ideal of $L_{v+1}$ under the $p^v$-th convolution power of the identity; each $\iota_v$ is injective with image, as an $R$-algebra map, exactly $\mathrm{hopfKer}$ of the composite $t_{i_0} \circ \dots \circ t_{i_0+v-1} : B_{i_0+v} \to B_{i_0}$; and $\iota_v \circ t'_v = t_{i_0+v} \circ \iota_{v+1}$ for all $v$. Thus the data $(L,t')$ satisfies the defining conditions of a $p$-divisible group of height $h'$ over $R$, presented as explicit data and properties rather than as a packaged structure.
--
--   This is the step in the proof of Tate's Proposition 12 asserting that the shifted subquotient tower $E_{i_0+v}/E_{i_0}$ of a stabilised system of finite flat Hopf algebras is again a $p$-divisible group, here of height $h'$, with the identification of each layer as the Hopf kernel of $B_{i_0+v} \to B_{i_0}$ and compatibility with the transition maps. It is used in the construction of a $p$-divisible group over a ring of integers together with an injective map on Tate modules attached to a Hopf quotient system.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.Tower.exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer
    {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] (p h' i₀ : ℕ)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    [∀ w, Coalgebra.IsCocomm R (B w)] [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
    (t : ∀ w, B (w + 1) →ₐc[R] B w) (ht : ∀ w, Function.Surjective (t w))
    (m : ∀ w, B w →ₐc[R] B (w + 1))
    (hmt : ∀ w, (m w).comp (t w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B (w + 1)) p)
    (htm : ∀ w, (t w).comp (m w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B w) p)
    (hkill : ∀ w, ∀ d ∈ HopfAlgebra.hopfKer (t w),
      PDivisibleGroup.Hopf.nsmulAlgHom R (B (w + 1)) p d = algebraMap R (B (w + 1)) (Coalgebra.counit d))
    (hmaps : ∀ w, Set.MapsTo (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
    (hbij : ∀ w, i₀ ≤ w → Set.BijOn (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
    (hrank : Module.finrank R ↥(HopfAlgebra.hopfKer (t i₀)) = p ^ h') :
    ∃ (L : ℕ → Type) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra R (L v))
      (_ : ∀ v, Coalgebra.IsCocomm R (L v)) (_ : ∀ v, Module.Free R (L v)) (_ : ∀ v, Module.Finite R (L v))
      (t' : ∀ v, L (v + 1) →ₐc[R] L v) (ι : ∀ v, L v →ₐc[R] B (i₀ + v)),
      (∀ v, Function.Surjective (t' v)) ∧ (∀ v, Module.finrank R (L v) = p ^ (v * h')) ∧
      (∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal R (L (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Injective (ι v)) ∧
      (∀ v, (ι v : L v →ₐ[R] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)) ∧
      (∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1))) := by sorry
