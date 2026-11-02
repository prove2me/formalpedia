-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_cdNorm_formula
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.cdNorm_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:59:26.420466+00:00
-- url     : https://prove2.me/theorems/949ea9ed-1fbf-4212-8d58-b7fba7d6800c
-- title:
--   Proposition 2: operational NS norm for classical-device states
-- statement:
--   All alphabets are finite and nonempty. Both conditional laws are nonnegative and normalized for every input, and each classical marginal is independent of Eve's input.
--
--   For any two compatible classical-device states $P_{CE\mid Z}$ and $Q_{CE\mid Z}$, the classical alphabet $C$ may be a tuple of arbitrarily many classical subsystems. The operational distance allows a random input $Z$ chosen after seeing $C$ and arbitrary stochastic processing of the resulting observation. Then
--
--   $$d_{\rm NS}(P,Q)=\frac12\sum_c\max_z\sum_e|P(c,e\mid z)-Q(c,e\mid z)|.$$
--
--   This formula characterizes the source's causal generating operations on classical-device states.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 24, Proposition 2 / equation (33)

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

/-- PDF p.24, Proposition 2, (33); maximization is inside the classical sum. -/
theorem cdNorm_formula {C E Z : Type}
    [Fintype C] [Fintype E] [Fintype Z] [Nonempty C] [Nonempty E] [Nonempty Z]
    (p q : CDArray C E Z) (hp : IsCD p) (hq : IsCD q) :
    cdDistance p q = (1 / 2 : ℝ) * ∑ c, finiteMax (fun z => ∑ e, |p z c e - q z c e|) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
