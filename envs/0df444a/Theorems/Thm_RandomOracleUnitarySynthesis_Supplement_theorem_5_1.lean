-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_Supplement_theorem_5_1
-- name    : RandomOracleUnitarySynthesis.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:38:10.217306+00:00
-- url     : https://prove2.me/theorems/3af78ccd-2ee2-4908-9670-554b4cd57e81
-- title:
--   Theorem 5.1 (companion theorem; not used in the proof of the goal) — Haar-interleaved random-phase design
-- statement:
--   For $N=2^n$, sample $H_1,\ldots,H_n$ independently from Haar probability on $U(N)$ and construct $\mu_H$ using $n+1$ independent uniformly random discrete phase layers as in Section 5. There exist an absolute constant $c>0$ and a threshold $n_0\ge3$ such that, for every $n\ge n_0$,
--
--   $$\Pr_H^*\left[\mu_H\text{ is not a }2^{-n^2/3}\text{-approximate strong adaptive }(N/8)\text{-design}\right]\le2^{-cn^2}.$$
--
--   The star denotes outer probability, so the statement bounds the bad set without a measurability assumption. Strong adaptive access includes all eight ordinary and controlled forward, inverse, conjugate and transpose oracles, with classical adaptive choices and arbitrary finite workspace. This companion theorem is not used in the proof of the retained goal.
--
--   Differences from the source:
--   - encoding: a distribution on U(N) and arbitrary strong adaptive quantum algorithms → a Borel probability on complex matrices with almost-sure unitary support and explicit CPTP algorithms with dephased oracle selectors; reason: the unitary inclusion identifies the same laws; selector dephasing and unrestricted finite workspace encode classical adaptive choice, outcomes and feedback
--   - encoding: probability at least 1 - 2^(-Omega(n^2)) of a good ensemble → outer measure of the bad set at most 2^(-c*n^2), with c>0 and n0>=3; reason: the proof gives a measurable eta_T upper bound containing the bad event; the integer query budget N/8 is exact from n>=3
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Theorem 5.1, printed p. 36 (PDF p. 38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf; published basis; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_Supplement_ensembles

open MeasureTheory
noncomputable section

namespace RandomOracleUnitarySynthesis.Supplement

/-- Theorem 5.1, printed p.36 / PDF p.38. The BAD set is bounded in outer
measure, avoiding an unproved measurability hypothesis. For n≥3 the natural
quotient 2^n/8 is exactly the paper's integer N/8. -/
theorem theorem_5_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (interleavingHaar n)
        {H | ¬ StrongDesign (phaseEnsemble (fun j => (H j : synthesis_Mat n)))
          (2^n / 8) (Real.rpow 2 (-((n : ℝ)^2)/3))} ≤
      ENNReal.ofReal (Real.rpow 2 (-c * (n : ℝ)^2)) := by sorry

end RandomOracleUnitarySynthesis.Supplement
