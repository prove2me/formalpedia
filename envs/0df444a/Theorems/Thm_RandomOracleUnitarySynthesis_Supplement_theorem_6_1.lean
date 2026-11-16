-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_Supplement_theorem_6_1
-- name    : RandomOracleUnitarySynthesis.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:38:54.547196+00:00
-- url     : https://prove2.me/theorems/1f1fdc4c-6480-4c38-8b6f-735d44c4bab7
-- title:
--   Theorem 6.1 (companion theorem; not used in the proof of the goal) — Hadamard random-phase design
-- statement:
--   For every integer $n\ge0$, set $N=2^n$. Construct $\mu$ with $n+1$ independent uniformly random discrete phase layers interleaved with exactly $n$ copies of the normalized $n$-qubit Hadamard. Then
--
--   $$\mu\text{ is a }2^{-n^2/4+4n}\text{-approximate strong adaptive unitary }\left\lfloor\frac{\sqrt N}{100}\right\rfloor\text{-design}.$$
--
--   Strong adaptive access allows all eight oracle variants, classical adaptive choice, arbitrary finite workspace, arbitrary mixed initial states and intermediate quantum operations. The result includes all small dimensions and zero-query cases, with no asymptotic threshold. This companion theorem is not used in the proof of the retained goal.
--
--   Differences from the source:
--   - encoding: a distribution on U(N) and arbitrary strong adaptive quantum algorithms → a Borel probability on complex matrices with almost-sure unitary support and explicit CPTP algorithms with dephased oracle selectors; reason: the unitary inclusion identifies the same laws; selector dephasing and unrestricted finite workspace encode classical adaptive choice, outcomes and feedback
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Theorem 6.1, printed p. 41 (PDF p. 43); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf; published basis; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_Supplement_ensembles

open MeasureTheory
noncomputable section

namespace RandomOracleUnitarySynthesis.Supplement

/-- Theorem 6.1, printed p.41 / PDF p.43, for EVERY n, including zero-query
and scalar cases. The floor, factor 100 and real accuracy exponent are exact. -/
theorem theorem_6_1 (n : ℕ) :
    StrongDesign (hadamardEnsemble n)
      ⌊Real.sqrt ((2 : ℝ)^n) / 100⌋₊
      (Real.rpow 2 (-((n : ℝ)^2)/4 + 4*(n : ℝ))) := by sorry

end RandomOracleUnitarySynthesis.Supplement
