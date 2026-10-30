-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JacobiCubeAnalyticToFormal_qPochInfPS_pow_three_eq_jacobiThetaPS_complex
-- name    : QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS_complex
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:39:02.372589+00:00
-- url     : https://prove2.me/theorems/f10f296d-4f61-4dc5-83ce-1af4ac7d4fdd
-- title:
--   Formal Jacobi identity over $\mathbb{C}$: $(q;q)_\infty^3=\sum_k(-1)^k(2k+1)q^{k(k+1)/2}$
-- statement:
--   In $\mathbb{C}[[X]]$,
--   $$\big((q;q)_\infty\big)^{3}=\sum_{k\ge0}(-1)^k(2k+1)\,X^{k(k+1)/2},$$
--   where $(q;q)_\infty$ is `qPochInfPS ℂ`, the inverse of the partition generating series, and the right-hand side is `jacobiThetaPS ℂ`. This is the formal power series version of Jacobi's identity. It is proved by showing both sides are Taylor series at $0$ of the same analytic function (the analytic Jacobi identity of Chapter 4), and uniqueness of power series expansions.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JacobiCubeAnalyticToFormal.lean#L282-L335

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Pending: B2 via analytic → formal Taylor bridge

Independent attack route on the cube convolution identity. Avoids
Sylvester's combinatorial bijection by leveraging the already-proved
**analytic** Jacobi cube identity from Chapter 4:

  `jacobiIdentity_pochhammer (q : ℂ) (hq : ‖q‖ < 1) :
       (eulerPentagonalInfiniteProduct q)^3
         = ∑' n : ℕ, ((-1)^n · (2n+1) · q^(n(n+1)/2))`

The plan: extract coefficient `n` from both sides via analytic Taylor
uniqueness, and identify both with the corresponding formal-PS coefficient.

## Roadmap

Let `f q := (eulerPentagonalInfiniteProduct q)^3` and
    `g q := ∑' n, (-1)^n (2n+1) q^{n(n+1)/2}`.
Both are analytic on `Metric.ball 0 1`, and equal there by
`jacobiIdentity_pochhammer`.

1. **Polynomial truncation agreement (analytic side).**  For `N > n`,
   `f q ≡ ((∏_{k=1}^N (1 - q^k))^3 : polynomial)  (mod q^{N+1})` near 0.
   *Reason*: the tail factors `∏_{k>N}(1 - q^k)` have constant coefficient
   1 and start at order > N, so they don't affect coefficients of degree
   ≤ N.

2. **Polynomial coefficient = formal-PS coefficient.**  For
   `P : ℂ[X]` and `n < deg(P)+1`, `P.coeff n` (polynomial) =
   `(P : ℂ⟦X⟧).coeff n` (formal PS) = analytic Taylor coefficient of
   `P.eval q` at `0`.

3. **Truncation = formal qPochInfPS truncation.**  Already proved as
   `coeff_qPochInfPS_pow_eq_coeff_finite_product_pow`.

4. **RHS Taylor extraction.**  The Taylor coefficient at `0` of `g`
   of order `n` equals `((jacobiTripleSign n : ℤ) : ℂ)` — by index
   unpacking and dominated convergence on the geometric tail.

5. **Combine via analytic uniqueness.**  `HasFPowerSeriesAt.eq_formal-
   MultilinearSeries_of_eventually` (Mathlib) gives that the formal
   multilinear series at 0 of `f` and `g` coincide, hence their
   coefficient functions agree.

Substantial Mathlib infrastructure (`HasFPowerSeriesAt`,
`AnalyticAt.taylor`, `Polynomial.hasFPowerSeries`) is involved. Each
step below is a cleanly-stated sorry; closing them is multi-day Lean
work but follows standard analytic patterns.

Once all five are closed, the headline goal in
`Pending/Chapter19_B2_FromCubeConvolution.lean` follows in two lines
(rewrite + ext, matched against this file's bridge theorems).
-/

open QseriesFormalization

open QseriesFormalization.PartI.Ch04 (eulerPentagonalInfiniteProduct
  )
open QseriesFormalization.PartIV.Ch19 (qPochInfPS jacobiThetaPS jacobiTripleSign
   
  )

/-! ### Step 1: polynomial truncation agreement

For each `n`, there exists `N` such that
  `fAnalytic q = ((∏_{k=0}^{N-1} (1 - q^(k+1)))^3) + (higher order tail)`
where the tail contributes 0 to the coefficient of `q^n` for `n < N`.

The right Lean machinery: `HasFPowerSeriesOnBall` + tail estimates.
-/

/- **Step 1.** The analytic Taylor coefficient at `0` of `fAnalytic` of
order `n` equals the polynomial coefficient at order `n` of the finite
truncation `(∏_{k=0}^{n}(1 - X^(k+1)))^3 ∈ ℂ[X]`.

Statement deferred until the Mathlib idiom is fixed (one of
`iteratedFDeriv`, `HasFPowerSeriesAt`, `Analytic.taylorCoeff`).  A
placeholder `True` here would violate the playbook (trivially-true
RHS), so we leave the precise statement out of the file and document
it here as the next concrete dependency. -/

/-! ### Step 2: polynomial coefficient = formal PS coefficient.

This direction is essentially `Polynomial.coe_powerSeries` plus
`Polynomial.coeff_coe` or `PowerSeries.coeff_polynomial`. Mathlib has
the natural ring hom `ℂ[X] →+* ℂ⟦X⟧` (`Polynomial.toPowerSeries`) and
it preserves coefficients.
-/

/-! ### Step 3: truncation = formal qPochInfPS truncation.

Already proved in `Chapter19.coeff_qPochInfPS_pow_eq_coeff_finite_product_pow`.
-/

/-! ### Step 4: RHS Taylor extraction. **CLOSED.**

The reindex `∑' k, jacobiTripleSign k · q^k = ∑' n, (-1)^n (2n+1) q^{T_n}`
is now proved unconditionally in `Chapter19_JacobiTripleSignChar` as
`tsum_jacobiTripleSign_eq_jacobi_series`. -/

/-! ### Step 5: combine via analytic uniqueness.

`Mathlib.Analysis.Analytic.Uniqueness.HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually`
gives: if `f` and `g` are analytic at `0` with formal multilinear series
`p` and `q` respectively, and `f = g` eventually near `0`, then `p = q`.

Applied here: `fAnalytic` has formal series `ofScalars ℂ (jts ·)` on
`ball 0 1` (the `hasFPowerSeriesOnBall_fAnalytic` below); the formal-PS
`(qPochInfPS ℂ) ^ 3` is also an analytic-PS at 0 (via its coefficients
matching a polynomial truncation up to high order).  By the uniqueness
of formal multilinear series for an analytic function, the coefficient
sequences coincide. -/

theorem QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS_complex :
    (qPochInfPS ℂ) ^ 3 = jacobiThetaPS ℂ := by sorry
