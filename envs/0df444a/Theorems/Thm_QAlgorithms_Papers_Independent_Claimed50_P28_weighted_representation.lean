-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_weighted_representation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.weighted_representation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:23:44.036484+00:00
-- url     : https://prove2.me/theorems/8db0ef26-1490-4633-aa44-08ba522942f8
-- title:
--   Block-invariant representation inverse-trace identity
-- statement:
--   Let $d\ge2$ and let positive nonzero seeds of total trace $d$ have Haar frame $F=P_1+AP_2+BP_3+CP_4$ with $A,B,C>0$. Let $G=\sum_{j=1}^4 g_jP_j$ with $g_j\ge0$. Then $G$ is positive semidefinite, and
--
--   $$\operatorname{Tr}(F^{-1}G)=g_1+(d^2-1)\left(\frac{g_2}{A}+\frac{g_3}{B}+\frac{(d^2-1)g_4}{C}\right).$$
--
--   The $P_j$ are the paired-wire sectors of (28), with dimensions $1,d^2-1,d^2-1,(d^2-1)^2$. This gives the weighted loss expression used for further minimization. It does not assert a weighted optimal seed or parameters absent from the source.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 4, (37)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.4, (37): the block-invariant weighted inverse trace, without an unspecified
weighted global optimizer. Positive A,B,C ensure the displayed full inverse is valid. -/
theorem weighted_representation {d : ℕ} (hd : 2 ≤ d) {J : Type*} [Fintype J]
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (P : J → Op (ChoiBasis d)) (hP : Seeds P) (g : Fin 4 → ℝ) (hg : ∀ j, 0 ≤ g j)
    (hA : 0 < coefficientA P) (hB : 0 < coefficientB P) (hC : 0 < coefficientC P) :
    let G := ∑ j, (g j : ℂ) • sector d j
    G.PosSemidef ∧
    ((twirledFrame haar P)⁻¹ * G).trace.re = g 0 + ((d : ℝ)^2 - 1) *
      (g 1 / coefficientA P + g 2 / coefficientB P +
        ((d : ℝ)^2 - 1) * g 3 / coefficientC P) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
