-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_7_2
-- name    : RQCMoments.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:55:23.961146+00:00
-- url     : https://prove2.me/theorems/0a10488b-b57e-4175-9c71-f86c30b26b6e
-- title:
--   Theorem 7.2 — mean output entropy of a design is within $4\sqrt{3\eta}/(e\ln2)$ of Haar
-- statement:
--   For $\varepsilon\in[0,1]$ and $k\ge1$, let $\mu(k,\varepsilon)$ be any $n$-qubit $\varepsilon$-approximate $k$-design and $\mu$ the Haar measure. Let $S(U)$ be the Shannon entropy of the output distribution of $U$, and let $\eta=\eta(k,\varepsilon)$ be the maximum over $x\in\{0,1\}^n$ of the Kolmogorov distance between the law of $P_x$ for $U\sim\mu(k,\varepsilon)$ and that for $U\sim\mu$. Then
--
--   $$\Big|\mathbb E_{U\sim\mu(k,\varepsilon)}[S]-\mathbb E_{U\sim\mu}[S]\Big|\le\frac{4\sqrt{3\eta}}{e\ln2}.$$
--
--   Combined with the base mission's Theorem 4.9, which bounds $\eta$, this shows that designs reproduce the Haar value of the expected output entropy.
--
--   **Formalization Note** $P_x=|\langle x|U|y\rangle|^2$ for an input $y$; the statement is for every $y$ (the proof takes $y=0$). $S$ is in bits. The design is `IsStrongDesign μ k k ε`; Haar is `QAlgorithms.Schur.unitaryHaar (2^n)`.
--
--   Differences from the source:
--
--   - generalization: a fixed input y (the proof takes y = 0) → every input y : Fin (2^n); reason: §1 fixes an arbitrary input; the Lean statement specializes to y = 0 and to any fixed y
--   - encoding: ε-approximate unitary k-design (Remark 2.3) → IsStrongDesign μ k k ε (published; probability measure, literal completely positive order); reason: Remark 2.3 fixes this meaning; same instances
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 7.2, (319), p.63 (PDF p.65); §1, p.4

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_Supplement_outputEntropy

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 7.2** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 7.2, (319), p.63, PDF p.65).
For `ε ∈ [0,1]` and `k ≥ 1`, let `μ(k, ε)` be the distribution of any `n`-qubit `ε`-approximate
`k`-design, and `μ` the Haar measure. Let `S = S(U)` be the Shannon entropy of the output distribution
of `U`, and let `η = η(k, ε)` be the maximum over `x ∈ {0,1}^n` of the Kolmogorov distance between the
law of `P_x` for `U ∼ μ(k, ε)` and that for `U ∼ μ`. Then
`|E_{μ(k,ε)}[S] − E_μ[S]| ≤ 4√(3η)/(e ln 2)` (319).

**Formalization Note** `P_x = |⟨x|U|y⟩|²` for a fixed input `y`; the paper fixes `y` in §1 and its
proof takes `y = 0`. The theorem is stated for every `y` (`outputEntropy y`, in bits, and
`entropyEta y`). `μ(k, ε)` is a measure on `U(2^n)` with `IsStrongDesign · k k ε` (Remark 2.3); Haar
is the published `QAlgorithms.Schur.unitaryHaar (2^n)`. `e = exp 1`, `ln 2 = Real.log 2`. -/
theorem theorem_7_2 (n k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (μ : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)) (hμ : IsStrongDesign μ k k ε) (y : Fin (2 ^ n)) :
    |∫ U, outputEntropy y U ∂μ - ∫ U, outputEntropy y U ∂(QAlgorithms.Schur.unitaryHaar (2 ^ n))| ≤
      4 * Real.sqrt (3 * entropyEta y μ (QAlgorithms.Schur.unitaryHaar (2 ^ n))) /
        (Real.exp 1 * Real.log 2) := by sorry

end Supplement

end RQCMoments
