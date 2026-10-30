-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_triple_trace_reduction
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.triple_trace_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:45:22.877125+00:00
-- url     : https://prove2.me/theorems/dee322c4-c9ab-4946-a43d-5be48dde2f57
-- title:
--   (3.23)–(3.24): triple mixed norm reduces to a marginal
-- statement:
--   For nonzero finite registers of dimensions $d,n,m$, let $W\ge0$ be an operator in the ordered register $1,3,2=\mathbb C^d\otimes\mathbb C^n\otimes\mathbb C^m$, and let $W_{13}$ be its partial trace over the last register. For $1\le p\le\infty$,
--
--   $$\|W_{132}\|_{L_1(M_d;L_p(M_n;L_1(M_m)))}=\|W_{13}\|_{(1,p)}.$$
--
--   The triple norm is defined from the inner operator space's actual matrix-level norms via (3.3). The positivity condition is inherited from (3.20) and (3.22), which the source uses in this reduction. This supplies the marginal reduction needed for the entropy argument.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 17, (3.23)–(3.24): triple mixed norm reduces to a marginal

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

/-- (3.23)–(3.24), PDF p.17: the iterated 1,p,1 norm of a PSD matrix
in 1,3,2 order reduces to its 1,3 marginal. Positivity comes from the reductions
(3.20),(3.22) used on this page; arbitrary nonpositive W would make the claim false. -/
theorem triple_trace_reduction {A D I : Type} [Fintype A] [Fintype D] [Fintype I]
    [Nonempty A] [Nonempty D] [Nonempty I] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (W : Mat (A × (D × I))) (hW : W.PosSemidef) :
    tripleSize 1 p 1 W = mixedSize 1 p (traceLast W) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
