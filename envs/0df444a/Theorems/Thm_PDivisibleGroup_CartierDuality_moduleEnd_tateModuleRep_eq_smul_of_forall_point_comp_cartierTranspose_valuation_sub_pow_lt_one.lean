-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_moduleEnd_tateModuleRep_eq_smul_of_forall_point_comp_cartierTranspose_valuation_sub_pow_lt_one
-- name    : PDivisibleGroup.CartierDuality.moduleEnd_tateModuleRep_eq_smul_of_forall_point_comp_cartierTranspose_valuation_sub_pow_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/18a43825-db22-5b3e-ad19-e43218ad2d25
-- title:
--   Cartier-transpose Frobenius twist forces A to act by a scalar
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with an algebra map to $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ`, and a valuation subring $P$ of $\overline{\mathbb Q}$ containing the image of $O$. Let $H,H'$ be $p$-divisible groups over $O$ of height parameter $h$ (families of finite free cocommutative Hopf $O$-algebras `level v` with surjective transition maps, ranks $p^{vh}$, and the $p^v$-torsion-ideal condition on kernels), and let $D$ be a Cartier duality between them, i.e. bialgebra isomorphisms $H'.\mathrm{level}\,v\simeq \mathrm{Dual}_O(H.\mathrm{level}\,v)$ compatible with transitions. Here [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) is the group of sequences $(x_n)$ in $M$ with $p^n x_n=0$ and $p\,x_{n+1}=x_n$. Assume given: a $\mathbb Z_p$-bilinear $B$ from $T_p(H(\overline{\mathbb Q}))\times T_p(H'(\overline{\mathbb Q}))$ to $T_p(\overline{\mathbb Q}^{\times})$ whose $v$-th component, for representatives $f,\psi$ at level $v$ of $x_v,y_v$, equals $D.\mathrm{pair}$ of $f$ and $\psi$; an $O$-automorphism $\varphi'$ of $\overline{\mathbb Q}$ and a scalar $c\in\mathbb Z_p$; transition-compatible families $a,\varepsilon$ of bialgebra endomorphisms of the levels of $H$ with $\varepsilon\circ\varepsilon=\varepsilon$ and $\varepsilon\circ a=a\circ\varepsilon$; $\mathbb Z_p$-linear operators $Aop,Eop$ on $T_p(H(\overline{\mathbb Q}))$ acting componentwise by precomposing representatives with $a$, resp. $\varepsilon$. Assume (twist) for every level $v$ and every $P$-integral point $\psi$ of $H'$ at level $v$ fixed by precomposition with the Cartier transpose of $\varepsilon_v$ through $D$, that $\psi$ composed with the Cartier transpose of $a_v$ agrees with $c\mapsto \psi(c)^p$ modulo the maximal ideal of $P$ (valuation of the difference $<1$); and assume (frob) that for every $x$ admitting at each index a representative congruent to the counit modulo the maximal ideal of $P$ and satisfying $Eop\,x=x$, and for all $y,z$ admitting at each index representatives $\psi,\chi$ at a common level with $\psi$ being $P$-integral, $\chi\equiv\psi^p$ modulo the maximal ideal, and both fixed by the $\varepsilon$-transpose, one has $B(\varphi'\cdot x,z)=c\,B(x,y)$, where $\varphi'$ acts componentwise on points. Then for every $x$ in $T_p(H(\overline{\mathbb Q}))$ whose components admit representatives congruent to the counit modulo the maximal ideal of $P$ and with $Eop\,x=x$, one has $Aop(\varphi'\cdot x)=c\,x$.
--
--   This is the $p$-divisible-group core of Wiles's identity expressing the arithmetic Frobenius as the cyclotomic character times the inverse of $U_p\langle d_0\rangle$ on the multiplicative part of the ordinary corner of a $p$-adic Tate module; $a$ plays the role of $U_p\langle d_0\rangle$ and $\varepsilon$ that of the ordinary projector. It is used in the corresponding statement about the Tate module of the Jacobian of a modular curve, where the twist and Frobenius-pairing hypotheses are supplied by the geometry at $p$; the proof combines the transposition formula for $D.\mathrm{pair}$ with the nondegeneracy of the Tate pairing over an algebraically closed field of characteristic zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_moduleEnd_tateModuleRep_eq_smul_of_forall_point_comp_cartierTranspose_valuation_sub_pow_lt_one.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.moduleEnd_tateModuleRep_eq_smul_of_forall_point_comp_cartierTranspose_valuation_sub_pow_lt_one
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} {H H' : PDivisibleGroup O p h} (D : H.CartierDuality H')
    (B : TateModule p (H.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (H'.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (Additive (AlgebraicClosure ℚ)ˣ))
    (hB : ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (y : TateModule p (H'.Points (AlgebraicClosure ℚ))) (v : ℕ)
        (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
        H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) v →
        H'.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul ψ) = (y : ℕ → H'.Points (AlgebraicClosure ℚ)) v →
        ((Additive.toMul ((B x y : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) : (AlgebraicClosure ℚ)) = D.pair (AlgebraicClosure ℚ) v f ψ)
    (φ' : (AlgebraicClosure ℚ) ≃ₐ[O] (AlgebraicClosure ℚ)) (c : ℤ_[p])
    (a ε : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (ha : ∀ v : ℕ, (H.transition v).comp (a (v + 1)) = (a v).comp (H.transition v))
    (hε : ∀ v : ℕ, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hεε : ∀ v : ℕ, (ε v).comp (ε v) = ε v)
    (hεa : ∀ v : ℕ, (ε v).comp (a v) = (a v).comp (ε v))
    (Aop Eop : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hA : (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
      ((Aop x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom f).comp (a w : H.level w →ₐ[O] H.level w))))))
    (hE : (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
      ((Eop x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom f).comp (ε w : H.level w →ₐ[O] H.level w))))))
    (htwist : ∀ (v : ℕ) (ψ : H'.Point (AlgebraicClosure ℚ) v),
      (∀ c : H'.level v, PDivisibleGroup.Point.toAlgHom ψ c ∈ P) →
      (PDivisibleGroup.Point.toAlgHom ψ).comp (((D.equiv v).symm : CartierDual O (H.level v) →ₐc[O] H'.level v).comp
          ((CartierDual.map (ε v)).comp (D.equiv v : H'.level v →ₐc[O] CartierDual O (H.level v))) :
            H'.level v →ₐ[O] H'.level v) = PDivisibleGroup.Point.toAlgHom ψ →
      ∀ c : H'.level v,
        P.valuation ((PDivisibleGroup.Point.toAlgHom ψ).comp (((D.equiv v).symm : CartierDual O (H.level v) →ₐc[O] H'.level v).comp
          ((CartierDual.map (a v)).comp (D.equiv v : H'.level v →ₐc[O] CartierDual O (H.level v))) :
            H'.level v →ₐ[O] H'.level v) c -
          PDivisibleGroup.Point.toAlgHom ψ c ^ p) < 1)

    (hfrob : ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))),
      (∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
        ∀ c : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f c -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1) →
      Eop x = x →
      ∀ (y z : TateModule p (H'.Points (AlgebraicClosure ℚ))),
        (∀ n : ℕ, ∃ (w : ℕ) (ψ χ : H'.Point (AlgebraicClosure ℚ) w),
          H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul ψ) = (y : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
          H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul χ) = (z : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
          (∀ c : H'.level w, PDivisibleGroup.Point.toAlgHom ψ c ∈ P) ∧
          (∀ c : H'.level w, P.valuation (PDivisibleGroup.Point.toAlgHom χ c -
            PDivisibleGroup.Point.toAlgHom ψ c ^ p) < 1) ∧
          (PDivisibleGroup.Point.toAlgHom ψ).comp (((D.equiv w).symm : CartierDual O (H.level w) →ₐc[O] H'.level w).comp
              ((CartierDual.map (ε w)).comp (D.equiv w : H'.level w →ₐc[O] CartierDual O (H.level w))) :
                H'.level w →ₐ[O] H'.level w) = PDivisibleGroup.Point.toAlgHom ψ ∧
          (PDivisibleGroup.Point.toAlgHom χ).comp (((D.equiv w).symm : CartierDual O (H.level w) →ₐc[O] H'.level w).comp
              ((CartierDual.map (ε w)).comp (D.equiv w : H'.level w →ₐc[O] CartierDual O (H.level w))) :
                H'.level w →ₐ[O] H'.level w) = PDivisibleGroup.Point.toAlgHom χ) →
        B (H.tateModuleRep (AlgebraicClosure ℚ) φ' x) z = c • B x y)

    (x : TateModule p (H.Points (AlgebraicClosure ℚ)))
    (hx : ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      ∀ c : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f c -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1)
    (hEx : Eop x = x) :
    Aop (H.tateModuleRep (AlgebraicClosure ℚ) φ' x) = c • x := by sorry
