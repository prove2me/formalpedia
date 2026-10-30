-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P20_advantage_criterion
-- name    : QAlgorithms.Papers.Independent.Bridge50.P20.advantage_criterion
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T15:00:10.547875+00:00
-- url     : https://prove2.me/theorems/6524e088-d00b-47a9-a565-aff36763682f
-- title:
--   Range and sign of the relative advantage parameter
-- statement:
--   Let $a$ and $b$ denote, respectively, a finite nonnegative squashed-entanglement cut cost and a finite nonnegative versatile cut cost, with $a+b>0$. Define $\mu=(a-b)/(a+b)$. Then
--
--   $$
--   -1\le\mu\le1,\qquad \mu>0\ \Longleftrightarrow\ b<a.
--   $$
--
--   This compares the cut-cost terms used in the small-error regime. It does not assert a finite-error comparison of bounds with different continuity corrections.
-- source:
--   Versatile relative entropy bounds for quantum networks, arXiv:1707.05543v2, PDF p. 16, §IV B, (49): relative advantage parameter

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P20

open QAlgorithms QAlgorithms.Entanglement

-- Reuse pinned accepted definitions; source-specific conventions are audited below.

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P53 (amplitudeDamping)

open QAlgorithms.Papers.Independent.Information100.P75 (mixedIdentity)

open QAlgorithms.Papers.Independent.Next46.P29 (zRotation)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1707.05543v2, PDF p.16, (49): the relative advantage lies in [-1,1]
and is positive exactly when the versatile cut cost is strictly smaller.
The zero-cost pair is excluded by the positive-sum hypothesis. -/
theorem advantage_criterion (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsum : 0 < a + b) :
    (-1 ≤ relativeAdvantage a b ∧ relativeAdvantage a b ≤ 1) ∧
      (0 < relativeAdvantage a b ↔ b < a) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P20

end
