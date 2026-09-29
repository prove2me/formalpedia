-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le
-- name    : WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/451e3198-f700-591c-aa7d-fef28dfd663d
-- title:
--   Pull-back by [n] has index at most n²
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra and $K$ algebraically closed, let $W$ be a Weierstrass curve over $F$ that is elliptic, and let $n$ be an integer. Write $L = (W⁄K).\mathrm{FunctionField}$ for the function field of the base change of $W$ to $K$, and let $\gamma =$ `genericPoint W K` be the point of $W$ over $L$ given by the generic coordinates. Assume `MulGood W K n`, that is: $n \bullet \gamma \neq 0$, and $n \bullet \gamma$ is not the image under base change from $K$ to $L$ of any point $P$ of $W⁄K$. Under this hypothesis the $K$-algebra endomorphism `mulPull W K n` of $L$ is the map obtained, by lifting to fraction fields, from the injective coordinate homomorphism attached to the point $n \bullet \gamma$. The conclusion is the conjunction of two assertions: $L$ is a finite-dimensional module over the subfield `(mulPull W K n).fieldRange`, the image of that endomorphism, and the degree $[L : (\text{mulPull } W\,K\,n).\mathrm{fieldRange}]$ is at most $|n|^2$. Only the upper bound is asserted, not the classical equality.
--
--   This is the function-field form of the statement that multiplication by $n$ on an elliptic curve has degree $n^2$: the pull-back $[n]^*$ exhibits the function field as an extension of index at most $n^2$ of its image. It feeds the study of endomorphisms of the function field, being used in [`WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq`](thm.html#WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq) and in [`WeierstrassCurve.Affine.exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul`](thm.html#WeierstrassCurve.Affine.exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le.lean

import Mathlib
import Definitions.Def_EllipticCurve_FunctionFieldPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hgood : MulGood W K n) : FiniteDimensional (mulPull W K n).fieldRange (W⁄K).FunctionField ∧ Module.finrank (mulPull W K n).fieldRange (W⁄K).FunctionField ≤ n.natAbs ^ 2 := by sorry
