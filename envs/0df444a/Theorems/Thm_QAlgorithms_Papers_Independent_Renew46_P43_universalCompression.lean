-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_universalCompression
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.universalCompression
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:28:42.883576+00:00
-- url     : https://prove2.me/theorems/91bd0a70-64eb-4072-ba4a-68c35a7e7172
-- title:
--   Theorem I.17: JHHH scheme Fe≥1−2(n+1)^d 2^(−n inf_(H(nu)≥R) D(nu||averageState)).
-- statement:
--   Let a finite pure-state source have average $\bar\rho$ on a $d$-dimensional system. For $R\ge0$ and $n>0$, take the JHHH projection onto the least common support of all exact spectral types of all states of entropy at most $R$, over all fine bases. Compress onto its nonzero range and decode by inclusion. Divergences are in bits; an empty constraint infimum is $+\infty$ and $2^{-n\infty}=0$.
--
--   $$
--   F_e\ge1-2(n+1)^d2^{-n\inf_{H(\nu)\ge R}D(\nu\Vert\bar\rho)}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 17, Theorem I.17

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

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Theorem I.17, PDF p.17: entanglement fidelity of the actual universal JHHH
range compression followed by inclusion. The proof's later Fbar notation is a slip;
the printed theorem states Fe, which is retained here. -/
theorem universalCompression {a d : ℕ} (S : PureSource a d)
    (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (V : Matrix (Fin n → Fin d) (Fin k) ℂ)
    (hisometry : Vᴴ * V = 1) (hrange : V * Vᴴ = universalProjector d n R) :
    sourceFe (copies n S.average) (conjSuperop V ∘ projectionEncoder V) ≥
      1 - 2 * (n+1 : ℝ)^d * divergenceTail n (highEntropyDivergence S.average R) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
