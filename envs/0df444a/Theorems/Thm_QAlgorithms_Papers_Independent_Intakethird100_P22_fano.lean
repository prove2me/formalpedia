-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_fano
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.fano
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:16:59.163009+00:00
-- url     : https://prove2.me/theorems/ae7bab45-e76f-4f41-9c25-ae329ca456eb
-- title:
--   Fano inequality for the actual decoder error
-- statement:
--   For a finite normalized joint law p on nonempty X and Y and any decoder f:Y -> X, let e=Pr[X != f(Y)]. Then H(X|Y) <= h_2(e)+e log_2(|X|-1), with the singleton branch evaluated as 0 log 0=0. All quantities, including e and H(X|Y), are computed from p.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 38, Equation (161)

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

/-- PDF p.38, (161): decoding error is computed from the joint law and f.
For a singleton X, error and conditional entropy are zero; 0 log 0 is zero. -/
theorem fano {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (p : X × Y → ℝ) (hp : IsLaw p) (f : Y → X) :
    let err := ∑ x, ∑ y, if x = f y then 0 else p (x,y)
    shannon p - shannon (fun y => ∑ x, p (x,y)) ≤
      QAlgorithms.binEntropy2 err + err * Real.logb 2 ((Fintype.card X : ℝ) - 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
