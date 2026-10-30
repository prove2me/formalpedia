-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_mixed_norm_formulas
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.mixed_norm_formulas
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:44:33.567715+00:00
-- url     : https://prove2.me/theorems/a07a6d5f-d875-4141-a4b2-c483f38b3f74
-- title:
--   (3.18)–(3.22): mixed norms, positivity reductions, and partial trace
-- statement:
--   Fix $1\le q\le p\le\infty$ and $1\le r\le\infty$ with $1/q=1/p+1/r$, taking $1/\infty=0$. For every complex $Y\in M_d\otimes M_n$, $d,n\ge1$,
--
--   $$\|Y\|_{(p,q)}=\sup_{A,B\ne0}\frac{\|(A\otimes I_n)Y(B\otimes I_n)\|_q}{\|A\|_{2r}\|B\|_{2r}},\qquad
--   \|Y\|_{(q,p)}=\inf_{Y=(A\otimes I_n)Z(B\otimes I_n)}\|A\|_{2r}\|B\|_{2r}\|Z\|_p.$$
--
--   For $Y\ge0$, both optimizations may be restricted to $A=B\ge0$, with $Z\ge0$ in the factorization. In addition, every $X\ge0$ satisfies
--
--   $$\|X\|_{(p,1)}=\|\operatorname{Tr}_2X\|_p,\qquad
--   \|X\|_{(1,p)}=\inf_{B\in\mathcal D_d}\|(B^{-(1-1/p)/2}\otimes I_n)X(B^{-(1-1/p)/2}\otimes I_n)\|_p.$$
--
--   The last objective is $+\infty$ if $\ker B\nsubseteq\ker\operatorname{Tr}_2X$; compatible singular $B$ use powers on the support. The formal multiplier suprema use equivalent homogeneous unit balls. These are the characterizations and positivity/partial-trace reductions (3.18)–(3.22).
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 16, (3.18)–(3.22): mixed norms, positivity reductions, and partial trace

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

/-- (3.18)–(3.22), PDF p.16: both optimizations, their positive reductions,
the partial trace formula, and the density variational formula. Here r=infinity is allowed. -/
theorem mixed_norm_formulas {D I : Type} [Fintype D] [Fintype I]
    [Nonempty D] [Nonempty I] (q p r : ℝ≥0∞)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hr : 1 ≤ r) (hexp : recip q = recip p + recip r) :
    (∀ Y : Mat (D × I), mixedSize p q Y = multiplierSize q r Y ∧
      mixedSize q p Y = factorSize p r Y ∧
      (Y.PosSemidef → multiplierSize q r Y = positiveMultiplierSize q r Y ∧
        factorSize p r Y = positiveFactorSize q p r Y)) ∧
    (∀ X : Mat (D × I), X.PosSemidef →
      mixedNorm p 1 X = schattenNorm p (traceRight X) ∧
      mixedSize 1 p X = ⨅ B : Mat D, densityObjective p X B) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
