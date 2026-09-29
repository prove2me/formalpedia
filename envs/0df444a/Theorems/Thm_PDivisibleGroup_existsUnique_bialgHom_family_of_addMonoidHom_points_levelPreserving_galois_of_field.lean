-- Prove2me | Theorems.Thm_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field
-- name    : PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/76ded2bf-797e-5e3b-91de-abe79e32486d
-- title:
--   Tate's full faithfulness over a characteristic-zero field, points form
-- statement:
--   Let $p$ be a prime, $K$ a field of characteristic zero and $L$ an algebraic closure of $K$. Let $G$ and $H$ be $p$-divisible groups over $K$ of heights $h$ and $h'$: families of finite free cocommutative commutative Hopf $K$-algebras $G.\mathrm{level}\,v$ with surjective bialgebra transition maps $G.\mathrm{level}(v+1)\to G.\mathrm{level}\,v$ whose kernels are the $p^v$-torsion ideals and with $\operatorname{rank}_K G.\mathrm{level}\,v=p^{vh}$, and likewise for $H$. Write $G.\mathrm{Point}\,L\,v$ for the $K$-algebra maps $G.\mathrm{level}\,v\to L$ under convolution and $G.\mathrm{Points}\,L$ for the direct limit of the additive groups $\mathrm{Additive}(G.\mathrm{Point}\,L\,v)$. Let $F:G.\mathrm{Points}\,L\to H.\mathrm{Points}\,L$ be an additive map such that for every $v$ and every $x\in G.\mathrm{Point}\,L\,v$ the element $F$ of the image of $x$ is the image of some $y\in H.\mathrm{Point}\,L\,v$, and such that $F(\tau\cdot z)=\tau\cdot F(z)$ for all $\tau\in L\simeq_{\mathrm{alg}[K]}L$ and all $z$. Then there is a family of $K$-bialgebra maps $\varphi_v:H.\mathrm{level}\,v\to G.\mathrm{level}\,v$ with $G.\mathrm{transition}\,v\circ\varphi_{v+1}=\varphi_v\circ H.\mathrm{transition}\,v$ for all $v$, such that $F$ sends the image of each $x\in G.\mathrm{Point}\,L\,v$ to the image of $x\circ\varphi_v$; and any family $(\varphi'_v)$ of $K$-bialgebra maps with this last property equals $(\varphi_v)$, uniqueness being asserted without assuming compatibility with the transition maps.
--
--   This is the characteristic-zero (generic fibre) half of Tate's full faithfulness theorem for $p$-divisible groups, stated in terms of Galois-equivariant, level-preserving maps of groups of $L$-points rather than of homomorphisms of group schemes. It is obtained by applying the corresponding statement for a single finite Hopf algebra, [`HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero`](thm.html#HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero), level by level, and feeds the version over a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field
    (p : ℕ) [Fact p.Prime]
    {K : Type} [Field K] [CharZero K]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    {h h' : ℕ} (G : PDivisibleGroup K p h) (H : PDivisibleGroup K p h')
    (F : G.Points L →+ H.Points L)

    (hFlev : ∀ (v : ℕ) (x : G.Point L v), ∃ y : H.Point L v,
      F (G.pointsMkAdd L v (Additive.ofMul x)) = H.pointsMkAdd L v (Additive.ofMul y))

    (hFgal : ∀ (τ : L ≃ₐ[K] L) (z : G.Points L), F (τ • z) = τ • F z) :
    ∃ φ : ∀ v : ℕ, H.level v →ₐc[K] G.level v,
      (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (H.transition v)) ∧
      (∀ (v : ℕ) (x : G.Point L v),
        F (G.pointsMkAdd L v (Additive.ofMul x)) =
          H.pointsMkAdd L v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[K] G.level v))))) ∧

      (∀ φ' : ∀ v : ℕ, H.level v →ₐc[K] G.level v,
        (∀ (v : ℕ) (x : G.Point L v),
          F (G.pointsMkAdd L v (Additive.ofMul x)) =
            H.pointsMkAdd L v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[K] G.level v))))) →
        φ' = φ) := by sorry
