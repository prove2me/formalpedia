-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self
-- name    : PDivisibleGroup.exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/b31daa53-a895-5015-891d-b2bc66541415
-- title:
--   Complementary idempotents split a p-divisible group
-- statement:
--   Let $p$ be a prime, let $O$ be a discrete valuation domain equipped with an $O$-algebra structure on $\overline{\mathbb{Q}}$, and let $H$ be a [`PDivisibleGroup O p h`](def/PDivisibleGroup_Basic.html#L199): a family of commutative $O$-Hopf algebras $H_v$ with cocommutative comultiplication, finite free over $O$ of rank $p^{vh}$, together with surjective bialgebra transition maps $H_{v+1}\to H_v$ whose kernels are the ideals $\mathrm{torsionIdeal}\,O\,H_{v+1}\,(p^v)$, the images of the augmentation ideals under the $p^v$-fold-sum algebra maps. Let $\varepsilon,\varepsilon'$ be families of bialgebra endomorphisms of the $H_v$ such that each $\varepsilon_v,\varepsilon'_v$ is idempotent under composition, $\varepsilon_v\circ\varepsilon'_v=\varepsilon'_v\circ\varepsilon_v$ equals the trivial endomorphism (unit after counit), the convolution product $\varepsilon_v*\varepsilon'_v$ is the identity, and both commute with the transitions. Assume $h_1+h_2=h$, that for every $v$ the set of $O$-algebra maps $x\colon H_v\to\overline{\mathbb{Q}}$ with $x\circ\varepsilon_v=x$ has cardinality $p^{vh_1}$, and likewise $p^{vh_2}$ for $\varepsilon'$. Then there exist $p$-divisible groups $H_1,H_2$ over $O$ of heights $h_1,h_2$, surjective bialgebra maps $\pi_i\colon H_v\to (H_i)_v$ commuting with the transitions, algebra maps $\sigma_i\colon (H_i)_v\to H_v$ with $\pi_1\circ\sigma_1=\mathrm{id}$, $\sigma_1\circ\pi_1=\varepsilon_v$, $\pi_2\circ\sigma_2=\mathrm{id}$, $\sigma_2\circ\pi_2=\varepsilon'_v$, and bijective bialgebra maps $\Theta_v\colon H_v\to (H_1)_v\otimes_O (H_2)_v$ given by $\Theta_v(b)=(\pi_1\otimes\pi_2)(\Delta b)$.
--
--   This is the standard splitting of a $p$-divisible group into a product under a pair of orthogonal idempotent endomorphisms complementary in the convolution group, in the form used to cut out an ordinary part by an idempotent; the resulting factors are the images $\varepsilon H$ and $\varepsilon' H$. It is used in the analysis of the reduction of a $p$-divisible group, where Frobenius and Verschiebung on the split pieces are compared with the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O (AlgebraicClosure ℚ)]
    {h : ℕ} (H : PDivisibleGroup O p h)
    (ε ε' : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hε : ∀ v, (ε v).comp (ε v) = ε v) (hε' : ∀ v, (ε' v).comp (ε' v) = ε' v)
    (hεε' : ∀ v, (ε v : H.level v →ₐ[O] H.level v).comp (ε' v : H.level v →ₐ[O] H.level v) =
      (Algebra.ofId O (H.level v)).comp (Bialgebra.counitAlgHom O (H.level v)))
    (hε'ε : ∀ v, (ε' v : H.level v →ₐ[O] H.level v).comp (ε v : H.level v →ₐ[O] H.level v) =
      (Algebra.ofId O (H.level v)).comp (Bialgebra.counitAlgHom O (H.level v)))
    (hsum : ∀ v, WithConv.toConv (ε v : H.level v →ₐ[O] H.level v) *
        WithConv.toConv (ε' v : H.level v →ₐ[O] H.level v) =
      WithConv.toConv (AlgHom.id O (H.level v)))
    (hεt : ∀ v, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hε't : ∀ v, (H.transition v).comp (ε' (v + 1)) = (ε' v).comp (H.transition v))
    (h₁ h₂ : ℕ) (hh : h₁ + h₂ = h)
    (hcard₁ : ∀ v, Nat.card {x : H.Point (AlgebraicClosure ℚ) v //
        (PDivisibleGroup.Point.toAlgHom x).comp (ε v : H.level v →ₐ[O] H.level v) =
          PDivisibleGroup.Point.toAlgHom x} = p ^ (v * h₁))
    (hcard₂ : ∀ v, Nat.card {x : H.Point (AlgebraicClosure ℚ) v //
        (PDivisibleGroup.Point.toAlgHom x).comp (ε' v : H.level v →ₐ[O] H.level v) =
          PDivisibleGroup.Point.toAlgHom x} = p ^ (v * h₂)) :
    ∃ (H₁ : PDivisibleGroup O p h₁) (H₂ : PDivisibleGroup O p h₂)
      (π₁ : ∀ v, H.level v →ₐc[O] H₁.level v) (π₂ : ∀ v, H.level v →ₐc[O] H₂.level v)
      (σ₁ : ∀ v, H₁.level v →ₐ[O] H.level v) (σ₂ : ∀ v, H₂.level v →ₐ[O] H.level v)
      (Θ : ∀ v, H.level v →ₐc[O] H₁.level v ⊗[O] H₂.level v),
      (∀ v, Function.Surjective (π₁ v)) ∧ (∀ v, Function.Surjective (π₂ v)) ∧
      (∀ v, (π₁ v).comp (H.transition v) = (H₁.transition v).comp (π₁ (v + 1))) ∧
      (∀ v, (π₂ v).comp (H.transition v) = (H₂.transition v).comp (π₂ (v + 1))) ∧
      (∀ v, (π₁ v : H.level v →ₐ[O] H₁.level v).comp (σ₁ v) = AlgHom.id O (H₁.level v)) ∧
      (∀ v, (σ₁ v).comp (π₁ v : H.level v →ₐ[O] H₁.level v) = (ε v : H.level v →ₐ[O] H.level v)) ∧
      (∀ v, (π₂ v : H.level v →ₐ[O] H₂.level v).comp (σ₂ v) = AlgHom.id O (H₂.level v)) ∧
      (∀ v, (σ₂ v).comp (π₂ v : H.level v →ₐ[O] H₂.level v) = (ε' v : H.level v →ₐ[O] H.level v)) ∧
      (∀ v, Function.Bijective (Θ v)) ∧
      (∀ v b, Θ v b = Algebra.TensorProduct.map (π₁ v : H.level v →ₐ[O] H₁.level v)
        (π₂ v : H.level v →ₐ[O] H₂.level v) (Coalgebra.comul (R := O) b)) := by sorry
