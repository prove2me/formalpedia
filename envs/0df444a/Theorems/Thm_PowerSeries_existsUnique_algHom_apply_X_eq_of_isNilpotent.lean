-- Prove2me | Theorems.Thm_PowerSeries_existsUnique_algHom_apply_X_eq_of_isNilpotent
-- name    : PowerSeries.existsUnique_algHom_apply_X_eq_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/145bd640-a03a-5ad3-819c-02239e180a05
-- title:
--   Unique evaluation of power series at a nilpotent element
-- statement:
--   Let $A$ be a commutative ring and $T$ a commutative ring carrying an $A$-algebra structure, and let $t \in T$ be nilpotent, i.e. $t^{N_0} = 0$ for some natural number $N_0$. The theorem asserts a conjunction. First, there is exactly one $A$-algebra homomorphism $\varphi : A[[X]] \to T$ from the power series ring over $A$ with $\varphi(X) = t$: existence of such a $\varphi$, and equality of any two such. Second — and this second clause holds for every $A$-algebra homomorphism $\varphi$ with $\varphi(X) = t$, not merely for the distinguished one — for every natural number $N$ with $t^N = 0$ and every $f \in A[[X]]$ one has $$\varphi(f) = \sum_{i < N} \mathrm{alg}_{A \to T}\bigl(\mathrm{coeff}_i(f)\bigr)\, t^{\,i},$$ the sum running over $i$ in `Finset.range N`, where $\mathrm{coeff}_i(f)$ is the $i$-th coefficient of $f$ and $\mathrm{alg}_{A \to T}$ the structure map. Thus the unique homomorphism is truncated evaluation at $t$, and the formula is valid for every exponent $N$ killing $t$, not only for one particular choice.
--
--   This is the substitution principle for formal power series in the nilpotent (discrete, hence topology-free) case: $A[[X]]$ behaves as the free $A$-algebra on one nilpotent generator. It is used in the construction of lifts of formal-group data, being cited by [`FormalGroup.IsDrinfeldBasisAdic.exists_algHom_powerSeries_lift_of_smallExtension_of_sqZero`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_algHom_powerSeries_lift_of_smallExtension_of_sqZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_existsUnique_algHom_apply_X_eq_of_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.existsUnique_algHom_apply_X_eq_of_isNilpotent
    {A : Type} [CommRing A] {T : Type} [CommRing T] [Algebra A T] (t : T) (ht : IsNilpotent t) :
    (∃! φ : PowerSeries A →ₐ[A] T, φ PowerSeries.X = t) ∧
    (∀ φ : PowerSeries A →ₐ[A] T, φ PowerSeries.X = t → ∀ N : ℕ, t ^ N = 0 →
      ∀ f : PowerSeries A, φ f = ∑ i ∈ Finset.range N, algebraMap A T (PowerSeries.coeff i f) * t ^ i) := by sorry
