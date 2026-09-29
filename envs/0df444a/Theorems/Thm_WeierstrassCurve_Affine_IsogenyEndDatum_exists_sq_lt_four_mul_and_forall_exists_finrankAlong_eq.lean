-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq
-- name    : WeierstrassCurve.Affine.IsogenyEndDatum.exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/cac63699-df2c-5ce8-9951-0c3825b27434
-- title:
--   Non-integral isogeny endomorphism forces an imaginary quadratic degree form
-- statement:
--   Let $F$ be a field of characteristic zero with decidable equality which is algebraically closed, and let $W$ be an affine Weierstrass curve over $F$ which is elliptic, equipped with the gates `GenusOnePlaceGate W` (a bijection between $W.Point$ and the places of $W.FunctionField$ over $F$, all of which have degree $1$), `AbelTheorem W` (a degree-zero divisor is principal exactly when its image under `divisorSum` vanishes) and `GenusOnePlaceGate.IsCentred W` (for each nonsingular affine point the classes of $X$ and of $Y - y$ lie in the nonunits of the valuation subring of the place attached to that point). An `IsogenyEndDatum W` consists of an $F$-algebra endomorphism $\iota$ of $W.FunctionField$ which is integral and finite, i.e. makes $W.FunctionField$ a finite-dimensional module over itself along $\iota$; its degree is `finrankAlong F D.ι`, that dimension, and `D.pointEnd` is the induced endomorphism of $W.Point$ obtained from the Picard pushforward. Assume `hNs`: every isogeny end datum satisfies the pushforward norm formula, i.e. for every nonzero $f$ the pushforward of the principal divisor of $f$ is the divisor of $\mathrm{N}(f)$. Assume given one datum $D_0$ whose endomorphism of $W.Point$ is not $P \mapsto m \cdot P$ for any integer $m$. Then there are integers $t, n$ with $t^2 < 4n$ such that for all integers $a$ and $b$ with $b \neq 0$ some isogeny end datum $D$ has degree exactly $a^2 + tab + nb^2$. Only the realisation of these degrees is asserted, not that the corresponding endomorphism is $a + b\,[D_0]$.
--
--   This is the degree-form half of the classical statement that an elliptic curve carrying a non-integral endomorphism has complex multiplication by an order in an imaginary quadratic field, the degree being the (positive definite) norm form of that order. It is used in the proofs that, under suitable hypotheses on the $j$-invariant, every isogeny end datum acts on points as multiplication by an integer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_DualIsogenyAPI

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.IsogenyEndDatum.exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    [GenusOnePlaceGate.IsCentred W]
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    (D₀ : IsogenyEndDatum W) (hD₀ : ¬ ∃ m : ℤ, ∀ P : W.Point, D₀.pointEnd (hNs D₀) P = m • P) :
    ∃ t n : ℤ, t ^ 2 < 4 * n ∧
      ∀ a b : ℤ, b ≠ 0 → ∃ D : IsogenyEndDatum W,
        (finrankAlong F D.ι : ℤ) = a ^ 2 + t * a * b + n * b ^ 2 := by sorry
