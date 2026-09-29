-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_linearMap_tateModule_injective_of_surjective_comp_transition
-- name    : PDivisibleGroup.exists_linearMap_tateModule_injective_of_surjective_comp_transition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/c6ccfb04-dbe6-5398-8610-886764baf244
-- title:
--   Tate module functoriality for a surjection of p-divisible groups
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with an algebra structure on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and a valuation subring $P$ of $\overline{\mathbb{Q}}$. Let $H$ and $H_1$ be $p$-divisible groups over $O$ of heights $h$ and $h_1$, that is, towers of finite free cocommutative Hopf $O$-algebras `level v` with surjective transition maps, $O$-ranks $p^{vh}$ resp. $p^{vh_1}$, and the stated description of the kernels of the transitions. Let $\pi_v \colon H.\mathrm{level}\,v \to H_1.\mathrm{level}\,v$ be surjective morphisms of algebras and coalgebras satisfying $\pi_v \circ H.\mathrm{transition}_v = H_1.\mathrm{transition}_v \circ \pi_{v+1}$. Here the $\overline{\mathbb{Q}}$-points at level $v$ are the $O$-algebra maps $\mathrm{level}\,v \to \overline{\mathbb{Q}}$ under convolution, $\mathrm{Points}$ is the direct limit of these groups along the tower, and for an abelian group $M$ the Tate module $T(M)$ consists of the sequences $(x_n)$ in $M$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, a $\mathbb{Z}_p$-module. The assertion is that there is a $\mathbb{Z}_p$-linear map $j \colon T(H_1.\mathrm{Points}\,\overline{\mathbb{Q}}) \to T(H.\mathrm{Points}\,\overline{\mathbb{Q}})$ with five properties: $j$ is injective; $j$ is computed by precomposition with $\pi$, in the sense that whenever a level-$w$ point $f_1$ of $H_1$ represents the $n$-th component of $x$, the level-$w$ point $f_1 \circ \pi_w$ of $H$ represents the $n$-th component of $jx$; an element $y$ lies in the range of $j$ exactly when each component $y_n$ is represented by some level-$w$ point $f$ of $H$ annihilating $\ker \pi_w$; $j$ intertwines the actions of every $O$-algebra automorphism $\tau'$ of $\overline{\mathbb{Q}}$ on the two Tate modules, $j \circ H_1.\mathrm{tateModuleRep}(\tau') = H.\mathrm{tateModuleRep}(\tau') \circ j$; and, for each $x$, every component of $jx$ is represented by a level-$w$ point $f$ with $P\bigl(f(a) - \mathrm{counit}(a)\bigr) < 1$ for all $a$ if and only if the same holds for every component of $x$ with points of $H_1$.
--
--   This is the functoriality of the Tate module in the $p$-divisible group, in the form needed for a closed immersion $H_1 \hookrightarrow H$ of towers: the induced map on Tate modules is injective, Galois-equivariant, has the expected image, and detects reduction to the unit section at the place $P$. It is used in the comparison of Tate modules of a $p$-divisible group and of the image of an idempotent, feeding the identification of the Galois action on the Tate module with the cyclotomic character through the Frobenius–Verschiebung relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_linearMap_tateModule_injective_of_surjective_comp_transition.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_linearMap_tateModule_injective_of_surjective_comp_transition
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    {h h₁ : ℕ} (H : PDivisibleGroup O p h) (H₁ : PDivisibleGroup O p h₁)
    (π : ∀ v : ℕ, H.level v →ₐc[O] H₁.level v) (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v, (π v).comp (H.transition v) = (H₁.transition v).comp (π (v + 1))) :
    ∃ j : TateModule p (H₁.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (H.Points (AlgebraicClosure ℚ)),
      Function.Injective j ∧
      (∀ (x : TateModule p (H₁.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f₁ : H₁.Point (AlgebraicClosure ℚ) w),
        H₁.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f₁) =
          (x : ℕ → H₁.Points (AlgebraicClosure ℚ)) n →
        ((j x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f₁).comp (π w : H.level w →ₐ[O] H₁.level w))))) ∧
      (∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ LinearMap.range j ↔
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, π w a = 0 → PDivisibleGroup.Point.toAlgHom f a = 0) ∧
      (∀ τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ,
        j ∘ₗ H₁.tateModuleRep (AlgebraicClosure ℚ) τ' = H.tateModuleRep (AlgebraicClosure ℚ) τ' ∘ₗ j) ∧
      (∀ x : TateModule p (H₁.Points (AlgebraicClosure ℚ)),
        (∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (j x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ↔
        (∀ n : ℕ, ∃ (w : ℕ) (f : H₁.Point (AlgebraicClosure ℚ) w),
          H₁.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (x : ℕ → H₁.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H₁.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)) := by sorry
