-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_outer_amplification_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.outer_amplification_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:30:35.337761+00:00
-- url     : https://prove2.me/theorems/d01f5389-ae4d-4bba-9232-868029f673ce
-- title:
--   Lemma 5: amplification on the outer factor
-- statement:
--   Let $\Phi:M_m\to M_n$ be a complex-linear CP map and let $1\le q,p,r\le\infty$. For each ancillary dimension $d\ge1$, equip the tensor products with the vector-valued norms defined by (3.2)–(3.3). Then
--
--   $$\|\Phi\otimes\mathrm{id}_d\|_{(q,r)\to(p,r)}\le\|\Phi\|^+_{q\to p}.$$
--
--   The positive induced norm on the right optimizes over positive semidefinite inputs, and all Schatten traces are unnormalized. This controls amplification on the outer factor for arbitrary inner exponent $r$.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 11, Lemma 5: amplification on the outer factor

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

/-- Lemma 5 / (3.7), PDF pp.11–12: Phi acts on the outer factor, and r is arbitrary. -/
theorem outer_amplification_bound {I J D : Type} [Fintype I] [Fintype J] [Fintype D]
    [Nonempty I] [Nonempty J] [Nonempty D]
    (q p r : ℝ≥0∞) (hq : 1 ≤ q) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (Phi : (Mat I →ₗ[ℂ] Mat J)) (hPhi : Entanglement.IsCompletelyPositive Phi) :
    (⨆ X : {X : Mat (I × D) // mixedNorm q r X ≤ 1},
      ENNReal.ofReal (mixedNorm p r (tensorMap Phi (LinearMap.id : (Mat D →ₗ[ℂ] Mat D)) X.val))) ≤
      positiveInducedSize q p Phi := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
