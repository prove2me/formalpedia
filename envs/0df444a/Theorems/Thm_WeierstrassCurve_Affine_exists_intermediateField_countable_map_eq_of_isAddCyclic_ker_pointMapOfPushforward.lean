-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
-- name    : WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/0a40ab42-17dc-59b1-8b65-ce60e1b9c70a
-- title:
--   Cyclic degree-N function-field seams descend to countable subfields
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$, and let $E,E'$ be elliptic Weierstrass curves in affine form over $K$, each equipped with a `GenusOnePlaceGate` (a bijection between the group of points and the places of the function field over $K$, all places having degree $1$) which is centred (for every nonsingular $(x,y)$ the images of the classes of $X-x$ and $Y-y$ lie in the nonunits of the valuation subring of the place attached to the point $(x,y)$) and satisfying `AbelTheorem` (a divisor of degree $0$ is principal exactly when its divisor sum vanishes). Let $\iota : K(E') \to K(E)$ be a $K$-algebra homomorphism which is integral, makes $K(E)$ a finite module over $K(E')$, and satisfies the pushforward norm formula `NormFormulaAlong`. Let $N \neq 0$ be a natural number and assume the kernel of the induced homomorphism `pointMapOfPushforward` $\colon E(K) \to E'(K)$ (transport of the pushforward of degree-zero divisor classes along the two $\mathrm{Pic}^0$ identifications) is cyclic of cardinality $N$. Then, for the canonical $\mathbb{Q}$-algebra structure on $K$, there exist a countable intermediate field $K_0$ of $\mathbb{Q} \subseteq K$, elliptic Weierstrass curves $E_0,E_0'$ over $K_0$ whose base changes along $K_0 \to K$ are $E$ and $E'$ and whose base changes to $\overline{K_0}$ are elliptic, and an integral, finite $\overline{K_0}$-algebra homomorphism $\iota_0$ from the function field of $E_0' \times_{K_0} \overline{K_0}$ to that of $E_0 \times_{K_0} \overline{K_0}$, such that for every choice of gate, centredness and Abel data on the two base-changed affine curves and every witness of the pushforward norm formula for $\iota_0$, the kernel of the resulting `pointMapOfPushforward` is cyclic of cardinality $N$.
--
--   This is the first half of the Lefschetz-principle descent: the data of a finite function-field embedding with cyclic kernel of order $N$ is defined over a finitely generated, hence countable, subfield of $K$, and the conclusion is stated in the form that quantifies universally over the admissible genus-one gate data on the descended curves rather than supplying it. It feeds the transfer to $\mathbb{C}$ used in [`WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`](thm.html#WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward), which identifies the pair of $j$-invariants as a root of the modular polynomial of level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N) :
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∃ (K₀ : IntermediateField ℚ K) (_ : Countable K₀)
      (E₀ E₀' : WeierstrassCurve K₀) (_ : E₀.IsElliptic) (_ : E₀'.IsElliptic)
      (_ : E₀.map (algebraMap K₀ K) = E) (_ : E₀'.map (algebraMap K₀ K) = E')
      (_ : (E₀.baseChange (AlgebraicClosure K₀)).IsElliptic)
      (_ : (E₀'.baseChange (AlgebraicClosure K₀)).IsElliptic)
      (ι₀ : (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
        (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField)
      (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
      ∀ [DecidableEq (AlgebraicClosure K₀)]
        [GenusOnePlaceGate (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        (hN₀ : NormFormulaAlong (AlgebraicClosure K₀) ι₀ hfin₀),
        IsAddCyclic (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker ∧
          Nat.card (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker = N := by sorry
