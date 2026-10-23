-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_weakSourceConverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.weakSourceConverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:29:22.057916+00:00
-- url     : https://prove2.me/theorems/ae2947f5-80c6-49fe-b853-3c75e7d8659c
-- title:
--   Theorem I.18: liminf_(lambda→0+) Ra,Fbar(lambda)=liminf_(lambda→0+) Ra,Dbar(lambda)≥H(averageState).
-- statement:
--   For a finite pure-state iid source with average $\bar\rho$, let $R_{a,\bar F}(\lambda)$ and $R_{a,\bar D}(\lambda)$ be the fixed-error limsups of the minimum arbitrary-encoding block rates under average overlap or half-trace-distance error, respectively. The error limit below is from positive values.
--
--   $$
--   \liminf_{\lambda\downarrow0}R_{a,\bar F}(\lambda)=\liminf_{\lambda\downarrow0}R_{a,\bar D}(\lambda)\ge H(\bar\rho).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 18, Theorem I.18

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem I.18, PDF pp.18-19: one-sided error-to-zero liminf, not the value at zero. -/
theorem weakSourceConverse {a d : ℕ} (S : PureSource a d) :
    Filter.liminf (sourceRate S .arbitraryFidelity) (nhdsWithin 0 (Set.Ioi 0)) =
      Filter.liminf (sourceRate S .arbitraryDistortion) (nhdsWithin 0 (Set.Ioi 0)) ∧
    ENNReal.ofReal (vnEntropy S.average) ≤
      Filter.liminf (sourceRate S .arbitraryDistortion) (nhdsWithin 0 (Set.Ioi 0)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
