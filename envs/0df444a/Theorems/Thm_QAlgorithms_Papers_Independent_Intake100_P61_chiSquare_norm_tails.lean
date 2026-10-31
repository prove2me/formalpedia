-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P61_chiSquare_norm_tails
-- name    : QAlgorithms.Papers.Independent.Intake100.P61.chiSquare_norm_tails
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:08:08.967991+00:00
-- url     : https://prove2.me/theorems/515dd149-c649-4b7e-9f17-e60a37c52275
-- title:
--   Lemma 6: Laurent--Massart chi-square tails
-- statement:
--   Let n>0 and let Z_1,...,Z_n be independent standard real normal variables, with U=sum_i Z_i^2. For every real x>0, Pr[U-n>=2 sqrt(nx)+2x]<=exp(-x) and Pr[n-U>=2 sqrt(nx)]<=exp(-x). The finite product of Mathlib gaussianReal 0 1 constructs the actual law. The second event corrects the printed undefined X, as the source proof explicitly requires.
-- source:
--   Composable security proof for continuous-variable quantum key distribution with coherent states, arXiv:1408.5689v3, PDF p. 20, Lemma 6, E1; lower-tail correction pinned by p.21

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P61

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P61

attribute [local instance] Classical.propDecidable Classical.decEq

-- The frozen frequency formula specializes exactly to the source alphabet Fin (2 ^ d).

open QAlgorithms.Papers.Independent.Advance50.P30 (empiricalFrequency)

/-- PDF p.20, Lemma 6 (E1), Laurent--Massart: chi-square tails.
The law is constructed as the sum of squares of n independent N(0,1) coordinates.
Printed second event: U-X >= 2 sqrt(n*x), with X undefined.
Changed: n-U >= 2 sqrt(n*x), exactly the lower tail used on PDF p.21.
Positive degrees of freedom are explicit: at n=0 the inclusive lower event
would have probability one. Both source tail constants are preserved. -/
theorem chiSquare_norm_tails
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) :
    let law : Measure (Fin n → ℝ) :=
      Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
    law {z | (∑ i : Fin n, (z i) ^ 2) - (n : ℝ) ≥
      2 * Real.sqrt ((n : ℝ) * x) + 2 * x} ≤ ENNReal.ofReal (Real.exp (-x)) ∧
    law {z | (n : ℝ) - (∑ i : Fin n, (z i) ^ 2) ≥
      2 * Real.sqrt ((n : ℝ) * x)} ≤ ENNReal.ofReal (Real.exp (-x)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P61

end
