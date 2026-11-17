-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_7_8
-- name    : RQCMoments.Supplement.theorem_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:56:41.795401+00:00
-- url     : https://prove2.me/theorems/cf7442fe-29de-40c5-9340-6b9154e48fc5
-- title:
--   Theorem 7.8 — Chebyshev concentration of the output entropy of a design
-- statement:
--   Under the assumptions of Theorem 7.6, let $\eta$ be the single-entry Kolmogorov distance of Theorem 7.2, $\delta$ as in Definition 7.3, and $S_{\mathrm{Haar}}=\mathbb E_{U\sim\mu}[S]$ the expected entropy under Haar. Then for every $t>0$,
--
--   $$\Pr_{U\sim\mu(k,\varepsilon)}\Big[|S-S_{\mathrm{Haar}}|>t+\frac{4\sqrt{3\eta}}{e\ln2}\Big]\le\frac{2\,\mathrm{Var}_{U\sim\mu}[S]+578\,\delta^{1/2}}{t^2}=O\Big(\frac{1}{Nt^2}+\frac{\delta^{1/2}}{t^2}\Big),\qquad N=2^n .$$
--
--   The output entropy of a design concentrates around the Haar mean, which is what makes strong designs usable for certified randomness generation.
--
--   **Formalization Note** Both the inequality and the $O(\cdot)$ clause are stated; the $O$ is an absolute constant $C$ chosen before $n,k,\varepsilon,\mu,y,t$. $\mathrm{Var}_{U\sim\mu}$ is the Haar variance. The statement is for every input $y$.
--
--   Differences from the source:
--
--   - encoding: = O(1/(N t²) + δ^{1/2}/t²) → ∃ C > 0 (before n, k, ε, μ, y, t) with (2 Var + 578 δ^{1/2})/t² ≤ C·(1/(2^n t²) + δ^{1/2}/t²); reason: asymptotic notation with absolute constants chosen first; same content
--   - generalization: a fixed input y (the proof takes y = 0) → every input y : Fin (2^n); reason: §1 fixes an arbitrary input; the Lean statement specializes to y = 0 and to any fixed y
--   - encoding: ε-approximate unitary k-design (Remark 2.3) → IsStrongDesign μ k k ε (published; probability measure, literal completely positive order); reason: Remark 2.3 fixes this meaning; same instances
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 7.8, (350), p.68 (PDF p.70)

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_Supplement_outputEntropy

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 7.8** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 7.8, (350), p.68, PDF p.70).
Under the assumptions of Theorem 7.6 (`n ≥ 2`, `k ≥ 2`, `ε ∈ [0,1]`, `μ(k, ε)` any `n`-qubit
`ε`-approximate `k`-design, `μ` the Haar measure), let `η` be the single-entry Kolmogorov distance of
Theorem 7.2, `δ` as in Definition 7.3, and `S_Haar := E_μ[S]`. Then for every `t > 0`,
`Pr_{μ(k,ε)}[|S − S_Haar| > t + 4√(3η)/(e ln 2)] ≤ (2 Var_μ[S] + 578 δ^{1/2})/t² = O(1/(N t²) + δ^{1/2}/t²)`
(350), `N = 2^n`.

**Formalization Note** Both the inequality and the `O(·)` clause are stated; the `O(·)` is an absolute
constant `C` chosen before `n, k, ε, μ`, the input `y` and `t`. `Var_μ` is the Haar variance
(`ProbabilityTheory.variance`). The input `y` is fixed in the paper; the theorem is stated for every
`y`. `δ^{1/2} = √δ`; `e = exp 1`; `ln 2 = Real.log 2`. -/
theorem theorem_7_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ μ : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ), IsStrongDesign μ k k ε → ∀ y : Fin (2 ^ n),
        ∀ t : ℝ, 0 < t →
          (μ {U | t + 4 * Real.sqrt (3 * entropyEta y μ (QAlgorithms.Schur.unitaryHaar (2 ^ n))) /
                (Real.exp 1 * Real.log 2) <
              |outputEntropy y U -
                ∫ V, outputEntropy y V ∂(QAlgorithms.Schur.unitaryHaar (2 ^ n))|}).toReal ≤
            (2 * ProbabilityTheory.variance (outputEntropy y) (QAlgorithms.Schur.unitaryHaar (2 ^ n)) +
              578 * Real.sqrt (entropyDelta y μ (QAlgorithms.Schur.unitaryHaar (2 ^ n)))) / t ^ 2 ∧
          (2 * ProbabilityTheory.variance (outputEntropy y) (QAlgorithms.Schur.unitaryHaar (2 ^ n)) +
              578 * Real.sqrt (entropyDelta y μ (QAlgorithms.Schur.unitaryHaar (2 ^ n)))) / t ^ 2 ≤
            C * (1 / ((2 : ℝ) ^ n * t ^ 2) +
              Real.sqrt (entropyDelta y μ (QAlgorithms.Schur.unitaryHaar (2 ^ n))) / t ^ 2) := by sorry

end Supplement

end RQCMoments
