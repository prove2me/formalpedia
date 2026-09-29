-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_valuation_mulPull_le_of_ne_zero
-- name    : WeierstrassCurve.Affine.valuation_mulPull_le_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/1c1793dd-ad0d-5049-857d-4a582e939454
-- title:
--   Valuations along the multiplication-by-n pull-back of functions
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, $K$ algebraically closed and equipped with decidable equality, and let $W$ be a Weierstrass curve over $F$ which is elliptic; the coordinate ring of the base-changed affine curve `W⁄K` is assumed to be a Dedekind domain (these and the remaining typeclass assumptions are summarised here). Let $n$ be a natural number whose image in $K$ is nonzero, let $P$ be a point of `(W⁄K).Point` with $P \neq 0$ and $(n : \mathbb{Z}) \cdot P \neq 0$, let $h$ be an element of the function field `(W⁄K).FunctionField`, and let $k$ be a natural number. For a nonzero point $Q$, `placeOf W K Q` denotes the height-one prime of the coordinate ring of `W⁄K` given by the ideal `CoordinateRing.XYIdeal (W⁄K) Q.xc (C Q.yc)` cut out by the coordinates of $Q$ (maximal, hence prime, and nonzero). The hypothesis is that the valuation of $h$ at the place of $(n : \mathbb{Z}) \cdot P$ is at most $\mathrm{exp}(-k)$, i.e. at most the image of $-k$ under the embedding of $\mathbb{Z}$ into the multiplicative value group with zero. The conclusion is that the valuation at the place of $P$ of `mulPull W K n h` is also at most $\mathrm{exp}(-k)$, where `mulPull W K n` is the $K$-algebra endomorphism of `(W⁄K).FunctionField` obtained, when `MulGood W K n` holds (that is, $n$ times the generic point is nonzero and is not the base change of any $K$-point), by lifting the associated injective point homomorphism to the fraction field, and is the identity otherwise.
--
--   This is the statement that pull-back along multiplication by $n$ does not decrease the order of vanishing: a function vanishing to order at least $k$ at $nP$ pulls back to a function vanishing to order at least $k$ at $P$. It supplies the compatibility between $[n]^{*}$ and the adic valuations at closed points that is required in the construction of the pairing on $n$-torsion and in the proof of its non-degeneracy, and is used by [`WeierstrassCurve.Affine.eq_zero_of_forall_weilPairing0_eq_one`](thm.html#WeierstrassCurve.Affine.eq_zero_of_forall_weilPairing0_eq_one), [`WeierstrassCurve.Affine.exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul`](thm.html#WeierstrassCurve.Affine.exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul) and [`WeierstrassCurve.exists_pairing_torsionBy`](thm.html#WeierstrassCurve.exists_pairing_torsionBy).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_valuation_mulPull_le_of_ne_zero.lean

import Mathlib
import Definitions.Def_EllipticCurve_FunctionFieldPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem WeierstrassCurve.Affine.valuation_mulPull_le_of_ne_zero {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) (P : (W⁄K).Point) (hP : P ≠ 0) (hnP : (n : ℤ) • P ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ) (hh : (placeOf W K ((n : ℤ) • P) hnP).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) : (placeOf W K P hP).valuation (W⁄K).FunctionField (mulPull W K n h) ≤ exp (-(k : ℤ)) := by sorry
