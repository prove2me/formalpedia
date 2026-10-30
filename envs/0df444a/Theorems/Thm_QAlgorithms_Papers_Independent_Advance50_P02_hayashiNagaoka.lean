-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_hayashiNagaoka
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.hayashiNagaoka
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:19:17.709583+00:00
-- url     : https://prove2.me/theorems/6f745e90-aefe-46a3-a563-07e93b56172a
-- title:
--   Hayashi–Nagaoka operator inequality
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $c>0$, $0\le S\le I$, and $T\ge0$. Inverse square roots act as zero on the kernel. Then
--   $$I-(S+T)^{-1/2}S(S+T)^{-1/2}\le(1+c)(I-S)+(2+c+1/c)T.$$
--   This bounds the error operator of a pretty-good measurement.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 12, Lemma 10: Hayashi–Nagaoka operator inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Lemma 10, PDF p.12, background [17]: inverse square root is zero on the kernel. -/
theorem hayashiNagaoka (S T : Mat I) (hS : S.PosSemidef) (hSone : Below S 1)
    (hT : T.PosSemidef) (c : ℝ) (hc : 0 < c) :
    Below (1 - supportPower (S+T) (-(1/2 : ℝ)) * S * supportPower (S+T) (-(1/2 : ℝ)))
      (((1+c : ℝ) : ℂ) • (1-S) + ((2+c+1/c : ℝ) : ℂ) • T) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
