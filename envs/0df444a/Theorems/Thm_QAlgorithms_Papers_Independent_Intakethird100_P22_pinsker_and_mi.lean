-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_pinsker_and_mi
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.pinsker_and_mi
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:16:18.652642+00:00
-- url     : https://prove2.me/theorems/8fa2b2fb-d316-404e-a639-ec36b7e39654
-- title:
--   Pinsker inequality in bits and its mutual-information identity
-- statement:
--   For normalized laws p,q on a finite nonempty alphabet, TV(p,q)^2 <= D_bits(p||q)/2, with support failures retained as infinity. For any normalized finite joint law r, D_bits(r||r_A r_B)=I_r(A:B). The squared inequality is equivalent to the printed square-root form because TV is nonnegative.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 38, Equation (160) and following identity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P22

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel correlationMixture prBox)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Gap48.P25 (classicalMI)

/-- PDF p.38, (160) and the following MI identity. The displayed loose
Pinsker coefficient is in bits. Squaring preserves the inequality since TV is
nonnegative. Extended nonnegative reals retain infinity on support failure. -/
theorem pinsker_and_mi {I A B : Type}
    [Fintype I] [Fintype A] [Fintype B] [Nonempty I] [Nonempty A] [Nonempty B]
    (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q)
    (r : A × B → ℝ) (hr : IsLaw r) :
    ENNReal.ofReal (((1/2 : ℝ) * ∑ i, |p i - q i|) ^ 2) ≤
      QAlgorithms.Papers.Independent.Renew46.P37.classicalKL p q / 2 ∧
    QAlgorithms.Papers.Independent.Renew46.P37.classicalKL r
      (fun ab => (∑ b, r (ab.1,b)) * (∑ a, r (a,ab.2))) =
      ENNReal.ofReal (classicalMI r) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
