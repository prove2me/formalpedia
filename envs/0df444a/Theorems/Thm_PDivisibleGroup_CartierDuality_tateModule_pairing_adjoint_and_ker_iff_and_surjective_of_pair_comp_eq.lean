-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq
-- name    : PDivisibleGroup.CartierDuality.tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/6cb3adea-8927-56a6-aa35-6039c3624ae2
-- title:
--   Adjointness of Tate-module maps under Cartier pairings
-- statement:
--   Fix a commutative ring $R$, a prime $p$, and heights $h,h'$. Let $A,A'$ be $p$-divisible groups over $R$ of height $h$ together with a Cartier duality $D$ between them (a compatible family of coalgebra isomorphisms $A'.\mathrm{level}\,v \cong \mathrm{CartierDual}\,R\,(A.\mathrm{level}\,v)$), and likewise $\Gamma,\Gamma'$ of height $h'$ with a duality $E$. Let $L$ be an algebraically closed field of characteristic $0$ which is an $R$-algebra. Let $B$ be a $\mathbb{Z}_p$-bilinear map $\mathrm{TateModule}\,p\,(A.\mathrm{Points}\,L) \times \mathrm{TateModule}\,p\,(A'.\mathrm{Points}\,L) \to \mathrm{TateModule}\,p\,(\mathrm{Additive}\,L^\times)$, where $\mathrm{TateModule}\,p\,M$ is the group of sequences $(x_n)$ in $M$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, and assume $B$ computes the Cartier pairing levelwise: whenever $f \in A.\mathrm{Point}\,L\,v$ and $g \in A'.\mathrm{Point}\,L\,v$ represent the $v$-th components of $x$ and $y$ under the maps $\mathrm{pointsMkAdd}$ into the direct limits of point groups, the $v$-th component of $B\,x\,y$, viewed in $L$ via $L^\times$, equals $D.\mathrm{pair}\,L\,v\,f\,g$ (the pairing defined by the chosen basis of $A.\mathrm{level}\,v$ and $D$). Assume the same for a pairing $BE$ on the $\Gamma$-side relative to $E$. Let $\varphi$ be a family of coalgebra $R$-algebra maps $A.\mathrm{level}\,v \to \Gamma.\mathrm{level}\,v$ and $\psi$ a family $\Gamma'.\mathrm{level}\,v \to A'.\mathrm{level}\,v$, adjoint on $L$-points in the sense that for all $v$, $x \in \Gamma.\mathrm{Point}\,L\,v$ and $y \in A'.\mathrm{Point}\,L\,v$ one has $D.\mathrm{pair}\,L\,v\,(x \circ \varphi_v)\,y = E.\mathrm{pair}\,L\,v\,x\,(y \circ \psi_v)$, where the points are obtained by precomposing the corresponding algebra maps. Finally let $T\varphi : \mathrm{TateModule}\,p\,(\Gamma.\mathrm{Points}\,L) \to \mathrm{TateModule}\,p\,(A.\mathrm{Points}\,L)$ and $T\psi : \mathrm{TateModule}\,p\,(A'.\mathrm{Points}\,L) \to \mathrm{TateModule}\,p\,(\Gamma'.\mathrm{Points}\,L)$ be $\mathbb{Z}_p$-linear maps computed levelwise by precomposition with $\varphi$, resp. $\psi$: for all indices $n$ and all $w$, if a point $g$ at level $w$ represents the $n$-th component of $x$, then the $n$-th component of $T\varphi\,x$ is the class of $g \circ \varphi_w$, and symmetrically for $T\psi$. The conclusion is the conjunction of three assertions: (i) $B(T\varphi\,x, y) = BE(x, T\psi\,y)$ for all $x,y$; (ii) for every $y$, $T\psi\,y = 0$ if and only if $B(T\varphi\,x, y) = 0$ for all $x$; and (iii) if $T\varphi$ is injective and its range is saturated, i.e. $r \neq 0$ in $\mathbb{Z}_p$ and $r \cdot z \in \mathrm{range}\,T\varphi$ imply $z \in \mathrm{range}\,T\varphi$, then $T\psi$ is surjective.
--
--   This is the duality of homomorphisms of $p$-divisible groups passed to Tate modules: the Tate-module map of the Cartier-dual homomorphism is the transpose of $T\varphi$ under the two Tate pairings, its kernel is the annihilator of the image of $T\varphi$, and saturation of that image forces surjectivity. It is used in the construction of a $p$-divisible group together with a bialgebra homomorphism realising a prescribed kernel on Tate modules over a ring of integers, via the perfectness of the Tate pairing and the existence of $\mathbb{Z}_p$-bases of the Tate modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_CartierDuality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq
    {R : Type} [CommRing R] {p h h' : ℕ} [Fact p.Prime]
    {A A' : PDivisibleGroup R p h} (D : A.CartierDuality A')
    {Γ Γ' : PDivisibleGroup R p h'} (E : Γ.CartierDuality Γ')
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (B : TateModule p (A.Points L) →ₗ[ℤ_[p]] TateModule p (A'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hB : (∀ (x : TateModule p (A.Points L)) (y : TateModule p (A'.Points L)) (v : ℕ)
        (f : A.Point L v) (g : A'.Point L v),
        A.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → A.Points L) v →
        A'.pointsMkAdd L v (Additive.ofMul g) = (y : ℕ → A'.Points L) v →
        ((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = D.pair L v f g))
    (BE : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (Γ'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hBE : (∀ (x : TateModule p (Γ.Points L)) (y : TateModule p (Γ'.Points L)) (v : ℕ)
        (f : Γ.Point L v) (g : Γ'.Point L v),
        Γ.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → Γ.Points L) v →
        Γ'.pointsMkAdd L v (Additive.ofMul g) = (y : ℕ → Γ'.Points L) v →
        ((Additive.toMul ((BE x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = E.pair L v f g))
    (φ : ∀ v : ℕ, A.level v →ₐc[R] Γ.level v) (ψ : ∀ v : ℕ, Γ'.level v →ₐc[R] A'.level v)
    (hadj : ∀ (v : ℕ) (x : Γ.Point L v) (y : A'.Point L v),
      D.pair L v (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp
          (φ v : A.level v →ₐ[R] Γ.level v))) y =
        E.pair L v x (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp
          (ψ v : Γ'.level v →ₐ[R] A'.level v))))
    (Tφ : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (A.Points L))
    (hTφ : ∀ (x : TateModule p (Γ.Points L)) (n w : ℕ) (g : Γ.Point L w),
        Γ.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → Γ.Points L) n →
        ((Tφ x : TateModule p (A.Points L)) : ℕ → A.Points L) n =
          A.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ w : A.level w →ₐ[R] Γ.level w)))))
    (Tψ : TateModule p (A'.Points L) →ₗ[ℤ_[p]] TateModule p (Γ'.Points L))
    (hTψ : ∀ (y : TateModule p (A'.Points L)) (n w : ℕ) (g : A'.Point L w),
        A'.pointsMkAdd L w (Additive.ofMul g) = (y : ℕ → A'.Points L) n →
        ((Tψ y : TateModule p (Γ'.Points L)) : ℕ → Γ'.Points L) n =
          Γ'.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (ψ w : Γ'.level w →ₐ[R] A'.level w))))) :
    (∀ (x : TateModule p (Γ.Points L)) (y : TateModule p (A'.Points L)), B (Tφ x) y = BE x (Tψ y)) ∧
    (∀ y : TateModule p (A'.Points L), Tψ y = 0 ↔ ∀ x : TateModule p (Γ.Points L), B (Tφ x) y = 0) ∧
    ((Function.Injective Tφ ∧
        ∀ (r : ℤ_[p]) (z : TateModule p (A.Points L)), r ≠ 0 → r • z ∈ LinearMap.range Tφ →
          z ∈ LinearMap.range Tφ) →
      Function.Surjective Tψ) := by sorry
