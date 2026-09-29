-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one
-- name    : PDivisibleGroup.CartierDuality.tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/d97eabb1-a424-5ffa-b365-4be18e78ed74
-- title:
--   Frobenius on the ε-part of a Tate module via Cartier duality
-- statement:
--   Let $p$ be a prime, let $O$ be a commutative ring with an algebra map to $\overline{\mathbb Q}$, let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $\operatorname{im}(O)\subseteq P$, and let $H,H'$ be $p$-divisible groups over $O$ of height $h$ (families of finite free $O$-Hopf algebras `level v` with surjective transition maps, $\operatorname{finrank}=p^{vh}$), equipped with a Cartier duality datum $D$ identifying $H'_v$ with the Cartier dual of $H_v$ compatibly with the transitions and multiplication by $p$. Assume given bialgebra endomorphisms $\varepsilon_v$ of each $H_v$ commuting with the transition maps, and orthogonality on the $\varepsilon$-part: at each level $v$, if a point $f$ of $H_v$ over $\overline{\mathbb Q}$ (an $O$-algebra map $H_v\to\overline{\mathbb Q}$) satisfies $P.\mathrm{valuation}(f(a)-\mathrm{counit}(a))<1$ for all $a$ and $f\circ\varepsilon_v=f$, and a point $\psi$ of $H'_v$ satisfies the same valuation condition, then $D.\mathrm{pair}\,v\,f\,\psi=\sum_i f(e_i)\,\psi(e_i^{\vee})=1$ for the chosen basis $(e_i)$ of $H_v$. Let $B$ be a $\mathbb Z_p$-bilinear map from the Tate modules (sequences $(x_n)$ with $p^nx_n=0$, $px_{n+1}=x_n$) of $H(\overline{\mathbb Q})$ and $H'(\overline{\mathbb Q})$ to that of $\mathrm{Additive}\,\overline{\mathbb Q}^{\times}$, whose $v$-th component on classes represented at level $v$ by $f$ and $\psi$ equals $D.\mathrm{pair}\,v\,f\,\psi$, and which is equivariant for all $O$-automorphisms $\sigma$ of $\overline{\mathbb Q}$ acting componentwise on Tate modules. Let $\varphi$ be a $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ lying in the decomposition subgroup of $P$ and inducing $t\mapsto t^{p}$ on the residue field of $P$, and $\varphi'$ an $O$-automorphism with $\varphi'=\varphi$ pointwise. Let $x$ be in the Tate module of $H(\overline{\mathbb Q})$ such that each component $x_n$ is represented at some level $w$ by a point $f$ with $P.\mathrm{valuation}(f(a)-\mathrm{counit}(a))<1$ for all $a$ and $f\circ\varepsilon_w=f$, and let $y,z$ be in the Tate module of $H'(\overline{\mathbb Q})$ such that for each $n$ there are a level $w$ and points $\psi,\chi$ representing $y_n$ and $z_n$ with $\psi$ taking values in $P$ and $P.\mathrm{valuation}(\chi(a)-\psi(a)^{p})<1$ for all $a$. Then $B(\varphi'x,z)=\chi_{\mathrm{cyc},p}(\varphi)\cdot B(x,y)$, where $\chi_{\mathrm{cyc},p}(\varphi)\in\mathbb Z_p^{\times}$ is the value of the $p$-adic cyclotomic character of $\overline{\mathbb Q}$ at $\varphi$.
--
--   This is the $\varepsilon$-localised form of the computation of arithmetic Frobenius on the Tate module of an ordinary $p$-divisible group through the Cartier pairing: orthogonality between points reducing to the identity is required only on the part cut out by the endomorphisms $\varepsilon_v$, and the conclusion compares $\varphi'x$ paired against $z$ with the cyclotomic character times $x$ paired against $y$, where $z$ is a componentwise $p$-th-power approximation to $y$. It feeds the statement on the Tate module of the Jacobian of a modular curve at an ordinary prime, where the $U$ and diamond operators composed with Frobenius are identified with the cyclotomic character on the relevant submodule; the only project input used is the determination of the Galois action on the Tate module of the roots of unity, [`TateModule.nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq`](thm.html#TateModule.nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.CartierDuality.tateModule_pairing_rep_eq_cyclotomicCharacter_smul_pairing_of_isFrobeniusAt_of_comp_transition_of_forall_comp_eq_of_forall_valuation_sub_pow_lt_one
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} {H H' : PDivisibleGroup O p h} (D : H.CartierDuality H')

    (ε : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hεtr : ∀ v : ℕ, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))

    (horth : ∀ (v : ℕ) (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
      (∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (PDivisibleGroup.Point.toAlgHom f).comp (ε v : H.level v →ₐ[O] H.level v) =
        PDivisibleGroup.Point.toAlgHom f →
      (∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      D.pair (AlgebraicClosure ℚ) v f ψ = 1)

    (B : TateModule p (H.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]]
      TateModule p (H'.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (Additive (AlgebraicClosure ℚ)ˣ))
    (hB : ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (y : TateModule p (H'.Points (AlgebraicClosure ℚ)))
        (v : ℕ) (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v),
        H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) v →
        H'.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul ψ) = (y : ℕ → H'.Points (AlgebraicClosure ℚ)) v →
        ((Additive.toMul ((B x y : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) :
          AlgebraicClosure ℚ) = D.pair (AlgebraicClosure ℚ) v f ψ)
    (hBσ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ) (x : TateModule p (H.Points (AlgebraicClosure ℚ)))
        (y : TateModule p (H'.Points (AlgebraicClosure ℚ))) (v : ℕ),
        ((Additive.toMul ((B (H.tateModuleRep (AlgebraicClosure ℚ) σ x)
            (H'.tateModuleRep (AlgebraicClosure ℚ) σ y) : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) :
            (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
          σ (((Additive.toMul ((B x y : ℕ → Additive (AlgebraicClosure ℚ)ˣ) v) : (AlgebraicClosure ℚ)ˣ) :
            AlgebraicClosure ℚ)))

    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (φ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ)
    (hφφ' : ∀ t : AlgebraicClosure ℚ, φ' t = φ t) (hφ : P.IsFrobeniusAt φ p)

    (x : TateModule p (H.Points (AlgebraicClosure ℚ)))
    (hx : ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      (∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ∧
      (PDivisibleGroup.Point.toAlgHom f).comp (ε w : H.level w →ₐ[O] H.level w) =
        PDivisibleGroup.Point.toAlgHom f)

    (y z : TateModule p (H'.Points (AlgebraicClosure ℚ)))
    (hyz : ∀ n : ℕ, ∃ (w : ℕ) (ψ χ : H'.Point (AlgebraicClosure ℚ) w),
      H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul ψ) = (y : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
      H'.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul χ) = (z : ℕ → H'.Points (AlgebraicClosure ℚ)) n ∧
      (∀ a : H'.level w, PDivisibleGroup.Point.toAlgHom ψ a ∈ P) ∧
      ∀ a : H'.level w, P.valuation (PDivisibleGroup.Point.toAlgHom χ a -
        PDivisibleGroup.Point.toAlgHom ψ a ^ p) < 1) :
    B (H.tateModuleRep (AlgebraicClosure ℚ) φ' x) z =
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • B x y := by sorry
