-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
-- name    : PDivisibleGroup.CartierDuality.charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/727feb8d-26f5-58c8-90b5-bf9b44fca322
-- title:
--   Character element of a dual point: multiplicativity, naturality, tower compatibility
-- statement:
--   Let $R$ be a commutative ring, let $p,h$ be natural numbers, and let $G,G'$ be $p$-divisible groups over $R$ of height $h$ in the sense of the project (families of finite free cocommutative Hopf $R$-algebras `level v` of rank $p^{vh}$ with surjective coalgebra-algebra transition maps whose kernels are the $p^v$-torsion ideals), linked by a Cartier duality datum $D$: coalgebra-algebra isomorphisms $e_v\colon G'.\mathrm{level}\,v \xrightarrow{\sim} \mathrm{CartierDual}\,R\,(G.\mathrm{level}\,v)$ satisfying $e_v(\mathrm{transition}\,x)(\mathrm{transition}\,a)=e_{v+1}(x)(p\cdot a)$. Let $S$ be a commutative $R$-algebra and $v$ a natural number. Writing $(b_i)$ for the chosen basis of $G.\mathrm{level}\,v$ with coordinate functionals $(b^i)$, points of $G$ and $G'$ over $S$ being $R$-algebra maps from the level algebras to $S$ under convolution, and $u_\psi=D.\mathrm{charElem}\,S\,v\,\psi=\sum_i \psi(e_v^{-1}b^i)\otimes b_i \in S\otimes_R G.\mathrm{level}\,v$, $d\chi_\psi=D.\mathrm{charDiff}\,S\,v\,\psi$ its image under $1\otimes$ the cotangent class map in $S\otimes_R G.\mathrm{Cotangent}\,v$, the theorem asserts ten statements simultaneously: (i) $(1\otimes\varphi)(u_\psi)=\psi(e_v^{-1}\varphi)$ for every $R$-linear functional $\varphi$ on $G.\mathrm{level}\,v$, after the identification $S\otimes_R R\cong S$; (ii) for every point $f$ of $G$ over $S$, the algebra map $S\otimes_R G.\mathrm{level}\,v\to S$ lifting $\mathrm{id}_S$ and $f$ carries $u_\psi$ to the Cartier pairing $D.\mathrm{pair}\,S\,v\,f\,\psi$; (iii) $u_{\psi\psi'}=u_\psi u_{\psi'}$ and $u_1=1$; (iv) $d\chi_{\psi\psi'}=d\chi_\psi+d\chi_{\psi'}$ and $d\chi_1=0$; (v) naturality: for every commutative $R$-algebra $S'$ and $R$-algebra map $\sigma\colon S\to S'$, $\sigma\otimes\mathrm{id}$ sends $u_\psi$ to $u_{\sigma\circ\psi}$ and $d\chi_\psi$ to $d\chi_{\sigma\circ\psi}$, where $\sigma\circ\psi$ is `pointMap`; (vi) compatibility along the tower: if $\psi$ is a point of $G'$ over $S$ at level $v$ and $\psi_1$ one at level $v+1$ with $\mathrm{pointIncl}\,\psi=\psi_1^{p}$, then $1\otimes(G.\mathrm{transitionAlgHom}\,v)$ sends $u_{\psi_1}$ to $u_\psi$ and $1\otimes(G.\mathrm{cotangentMap}\,v)$ sends $d\chi_{\psi_1}$ to $d\chi_\psi$.
--
--   This packages the basic formal properties of the character of a point of the Cartier dual of a $p$-divisible group and of its differential at the origin, in the style of Tate's treatment: basis independence, identification with the Cartier pairing, multiplicativity in the point, additivity of the differential, base change in $S$, and compatibility with the transition maps of the tower together with multiplication by $p$ on the dual. It is used to construct the additive map from the Tate module of $G'$ to $S\otimes_R$ (cotangent space of $G$) in [`PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_apply_eq_charDiff`](thm.html#PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_apply_eq_charDiff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CharacterDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
    {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (S : Type) [CommRing S] [Algebra R S] (v : ℕ) :
    (∀ (ψ : G'.Point S v) (φ : Module.Dual R (G.level v)),
        TensorProduct.rid R S (φ.lTensor S (D.charElem S v ψ)) =
          Point.toAlgHom ψ ((D.toDualEquiv v).symm φ)) ∧
    (∀ (f : G.Point S v) (ψ : G'.Point S v),
        Algebra.TensorProduct.lift (AlgHom.id R S) (Point.toAlgHom f) (fun _ _ => .all _ _)
          (D.charElem S v ψ) = D.pair S v f ψ) ∧
    (∀ ψ ψ' : G'.Point S v, D.charElem S v (ψ * ψ') = D.charElem S v ψ * D.charElem S v ψ') ∧
    D.charElem S v 1 = 1 ∧
    (∀ ψ ψ' : G'.Point S v, D.charDiff S v (ψ * ψ') = D.charDiff S v ψ + D.charDiff S v ψ') ∧
    D.charDiff S v 1 = 0 ∧
    (∀ (S' : Type) [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S') (ψ : G'.Point S v),
        Algebra.TensorProduct.map σ (AlgHom.id R (G.level v)) (D.charElem S v ψ) =
          D.charElem S' v (G'.pointMap σ v ψ)) ∧
    (∀ (S' : Type) [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S') (ψ : G'.Point S v),
        TensorProduct.map σ.toLinearMap LinearMap.id (D.charDiff S v ψ) =
          D.charDiff S' v (G'.pointMap σ v ψ)) ∧
    (∀ (ψ : G'.Point S v) (ψ₁ : G'.Point S (v + 1)), G'.pointIncl S v ψ = ψ₁ ^ p →
        (G.transitionAlgHom v).toLinearMap.lTensor S (D.charElem S (v + 1) ψ₁) = D.charElem S v ψ) ∧
    (∀ (ψ : G'.Point S v) (ψ₁ : G'.Point S (v + 1)), G'.pointIncl S v ψ = ψ₁ ^ p →
        (G.cotangentMap v).lTensor S (D.charDiff S (v + 1) ψ₁) = D.charDiff S v ψ) := by sorry
