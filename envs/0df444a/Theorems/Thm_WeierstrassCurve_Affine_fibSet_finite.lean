-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_fibSet_finite
-- name    : WeierstrassCurve.Affine.fibSet_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/d1b840cd-018f-5bca-9508-90b9fb006ef1
-- title:
--   Fibres of multiplication by n are finite
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra and $K$ algebraically closed, let $W$ be a Weierstrass curve over $F$ which is elliptic, and let $n$ be a natural number whose image in $K$ is nonzero. Write $(W⁄K)$ for the base change of $W$ to $K$ and $(W⁄K)$`.Point` for its group of affine points together with the point at infinity. Then for every point $Q$ of $(W⁄K)$, the set `fibSet W K n Q`, that is $\{P : n \cdot P = Q\}$, the fibre over $Q$ of multiplication by the integer $n$ on $(W⁄K)$`.Point`, is finite. No claim is made about the cardinality of this fibre, nor about its non-emptiness; the assertion is finiteness alone, and in particular it holds vacuously when $Q$ is not divisible by $n$.
--
--   This is the finiteness half of the classical description of the fibres of the isogeny $[n]$ on an elliptic curve over an algebraically closed field of residue characteristic prime to $n$: a fibre is empty or a translate of the $n$-torsion subgroup, which has $n^2$ elements. It underlies the counting and valuation statements used in the construction of the Weil pairing, being cited by [`WeierstrassCurve.Affine.ncard_fibSet`](thm.html#WeierstrassCurve.Affine.ncard_fibSet) and by the lemmas on valuations of Weil functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_fibSet_finite.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem WeierstrassCurve.Affine.fibSet_finite {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) (Q : (W⁄K).Point) : (fibSet W K n Q).Finite := by sorry
