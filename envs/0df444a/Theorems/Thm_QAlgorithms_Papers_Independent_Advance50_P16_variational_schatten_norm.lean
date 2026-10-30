-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_variational_schatten_norm
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.variational_schatten_norm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:43:29.774902+00:00
-- url     : https://prove2.me/theorems/9631745f-ccf7-464e-b1e4-679f72e379ef
-- title:
--   (3.6): variational Schatten p-norm
-- statement:
--   Let $Y\ge0$ be a matrix on $\mathbb C^d\otimes\mathbb C^n$ with $d,n\ge1$, and let $1\le p\le\infty$. Write $A,B$ for densities on $\mathbb C^d$, taking $B$ positive definite and allowing $A$ to be singular. Then
--
--   $$\|Y\|_{(p,p)}=\inf_{B>0,\ \operatorname{Tr}B=1}\ \sup_{A\ge0,\ \operatorname{Tr}A=1}
--   \|(A^{1/(2p)}B^{-1/(2p)}\otimes I_n)Y(B^{-1/(2p)}A^{1/(2p)}\otimes I_n)\|_p.$$
--
--   The reciprocal of infinity is zero and the Schatten infinity norm is the operator norm. Restricting the outer optimization to invertible densities prevents a zero pseudoinverse from deleting input mass; the infimum has the source's value without requiring $Y$ to have full rank. This is the variational Schatten-norm principle of (3.6), using the Fubini identification.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 11, (3.6): variational Schatten p-norm

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- (3.6), PDF p.11: PSD Y, arbitrary exponent >=1 including infinity.
Invertible density B prevents a negative-power kernel from discarding Y. -/
theorem variational_schatten_norm {D I : Type} [Fintype D] [Fintype I]
    [Nonempty D] [Nonempty I] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Y : Mat (D × I)) (hY : Y.PosSemidef) :
    mixedSize p p Y = ⨅ B : {B : Mat D // IsDensityMatrix B ∧ B.PosDef},
      variationalSize p Y B.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
