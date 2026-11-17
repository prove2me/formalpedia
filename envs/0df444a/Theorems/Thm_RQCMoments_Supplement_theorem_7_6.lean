-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_7_6
-- name    : RQCMoments.Supplement.theorem_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:55:57.097841+00:00
-- url     : https://prove2.me/theorems/5c872a46-c813-4687-9536-a6a313c9feb3
-- title:
--   Theorem 7.6 — standard deviation of the output entropy: $|\mathrm{Sd}_{\mathrm{design}}-\mathrm{Sd}_{\mathrm{Haar}}|\le17\delta^{1/4}\le C(k^{-1/2}+\varepsilon)^{1/4}$
-- statement:
--   For integers $n\ge2$, $k\ge2$ and $\varepsilon\in[0,1]$, let $\mu(k,\varepsilon)$ be any $n$-qubit $\varepsilon$-approximate $k$-design and $\mu$ the Haar measure, let $S$ be the Shannon entropy of the output distribution of $U$, and let $\delta=\delta(k,\varepsilon)$ be as in Definition 7.3. Then there is an absolute constant $C$ such that
--
--   $$\Big|\mathrm{Sd}_{U\sim\mu(k,\varepsilon)}[S]-\mathrm{Sd}_{U\sim\mu}[S]\Big|\le17\,\delta^{1/4}\le C\big(k^{-1/2}+\varepsilon\big)^{1/4},$$
--
--   where $\mathrm{Sd}$ denotes the standard deviation.
--
--   Together with Theorem 7.2 this controls the first two moments of the output entropy of a design by those of Haar.
--
--   **Formalization Note** Both inequalities are stated; $C$ is chosen before $n,k,\varepsilon,\mu$ and the input $y$. $\mathrm{Sd}=\sqrt{\mathrm{Var}}$ (Mathlib's `variance`; $S$ is bounded). The statement is for every input $y$.
--
--   Differences from the source:
--
--   - generalization: a fixed input y (the proof takes y = 0) → every input y : Fin (2^n); reason: §1 fixes an arbitrary input; the Lean statement specializes to y = 0 and to any fixed y
--   - encoding: ε-approximate unitary k-design (Remark 2.3) → IsStrongDesign μ k k ε (published; probability measure, literal completely positive order); reason: Remark 2.3 fixes this meaning; same instances
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 7.6, (333), p.66 (PDF p.68); Definition 7.3, p.64

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_Supplement_outputEntropy

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 7.6** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 7.6, (333), p.66, PDF p.68).
For integers `n ≥ 2` and `k ≥ 2` and `ε ∈ [0,1]`, let `μ(k, ε)` be the distribution of any `n`-qubit
`ε`-approximate `k`-design and `μ` the Haar measure, let `S` be the Shannon entropy of the output
distribution of `U`, and let `δ = δ(k, ε)` be as in Definition 7.3. Then there is an absolute constant
`C` such that `|Sd_{μ(k,ε)}[S] − Sd_μ[S]| ≤ 17 δ^{1/4} ≤ C (k^{−1/2} + ε)^{1/4}` (333), where `Sd` is the
standard deviation.

**Formalization Note** `C` is chosen before `n, k, ε, μ` and the input `y`. Both inequalities are
stated. `Sd = √Var`, with `ProbabilityTheory.variance` (`S` is bounded, `0 ≤ S ≤ n`, so the variance is
finite). The input `y` is fixed in the paper (`y = 0` in the proofs); the theorem is stated for every
`y`. `δ^{1/4}` and `(·)^{1/4}` are real powers of nonnegative numbers; `k^{−1/2} = 1/√k`. -/
theorem theorem_7_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ μ : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ), IsStrongDesign μ k k ε → ∀ y : Fin (2 ^ n),
        |Real.sqrt (ProbabilityTheory.variance (outputEntropy y) μ) -
            Real.sqrt (ProbabilityTheory.variance (outputEntropy y)
              (QAlgorithms.Schur.unitaryHaar (2 ^ n)))| ≤
            17 * entropyDelta y μ (QAlgorithms.Schur.unitaryHaar (2 ^ n)) ^ ((1 : ℝ) / 4) ∧
          17 * entropyDelta y μ (QAlgorithms.Schur.unitaryHaar (2 ^ n)) ^ ((1 : ℝ) / 4) ≤
            C * (1 / Real.sqrt k + ε) ^ ((1 : ℝ) / 4) := by sorry

end Supplement

end RQCMoments
