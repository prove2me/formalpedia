-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq
-- name    : PDivisibleGroup.exists_linearMap_tateModule_of_comp_transition_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/a8cf9b11-e6da-5f0a-8cde-1c7fa786c784
-- title:
--   Functoriality of the Tate module in transition-compatible level maps
-- statement:
--   Fix a prime $p$, a commutative ring $R$ and an $R$-algebra $L$ which is a field. Let $G$ and $\Gamma$ be $p$-divisible groups over $R$ of heights $h$ and $h'$, that is, systems of finite free cocommutative Hopf $R$-algebras `level v` with $\operatorname{rank}_R(\text{level } v)=p^{vh}$ together with surjective coalgebra-compatible transition maps $\text{level}(v+1)\to\text{level }v$ whose kernels are the prescribed torsion ideals. Let $\varphi_v\colon G.\text{level } v\to\Gamma.\text{level } v$ be bialgebra maps with $\varphi_v\circ G.\text{transition}_v=\Gamma.\text{transition}_v\circ\varphi_{v+1}$ for every $v$. For a $p$-divisible group the $L$-points at level $v$ are the $R$-algebra maps $\text{level } v\to L$ with the convolution group law, and `Points L` is the direct limit over $v$ of their additive copies; the Tate module of an abelian group $M$ is the group of sequences $(x_n)_{n\in\mathbb N}$ in $M$ with $p^nx_n=0$ and $px_{n+1}=x_n$. The assertion is that there exists a $\mathbb Z_p$-linear map $T\varphi$ from the Tate module of $\Gamma.\text{Points }L$ to that of $G.\text{Points }L$ such that, first, whenever $x$ is in the source, $n,w\in\mathbb N$ and $g$ is a level-$w$ point of $\Gamma$ whose class in the direct limit equals $x_n$, the $n$-th component of $T\varphi(x)$ is the class of the level-$w$ point of $G$ given by the composite of $\varphi_w$ with $g$; and second, $T\varphi$ commutes with the componentwise action of every $R$-algebra automorphism $\tau$ of $L$ on the two Tate modules.
--
--   This is the functoriality of the Tate module of a $p$-divisible group in a homomorphism of $p$-divisible groups, presented via a transition-compatible family of bialgebra maps on the level algebras, together with the fact that the induced map is equivariant for the automorphisms of the coefficient field. It is used in the construction of exact sequences and product decompositions of Tate modules attached to $p$-divisible groups over rings of integers, in particular by the statements on injective maps with prescribed image, on kernels, and on splitting a Tate module as a product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_linearMap_tateModule_of_comp_transition_eq
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (L : Type) [Field L] [Algebra R L]
    {h h' : ℕ} (G : PDivisibleGroup R p h) (Γ : PDivisibleGroup R p h')
    (φ : ∀ v : ℕ, G.level v →ₐc[R] Γ.level v)
    (hφ : ∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1))) :
    ∃ Tφ : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (G.Points L),
      (∀ (x : TateModule p (Γ.Points L)) (n w : ℕ) (g : Γ.Point L w),
        Γ.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → Γ.Points L) n →
        ((Tφ x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
          G.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ w : G.level w →ₐ[R] Γ.level w))))) ∧
      (∀ (τ : L ≃ₐ[R] L) (x : TateModule p (Γ.Points L)),
        Tφ (Γ.tateModuleRep L τ x) = G.tateModuleRep L τ (Tφ x)) := by sorry
