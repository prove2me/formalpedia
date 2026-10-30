-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_stabilizerGramEstimate
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.stabilizerGramEstimate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:25:35.350671+00:00
-- url     : https://prove2.me/theorems/445c92e8-59cd-4dc1-8632-7f775d20f926
-- title:
--   Near orthogonality of stabilizer tensor powers
-- statement:
--   Let $d$ be prime and $n,t\geq1$. Choose one normalized vector for each phase-free stabilizer density matrix and construct $G_{S,S^\prime}=\langle S|S^\prime\rangle^t$ and $Q=\sum_S|S\rangle^{\otimes t}\langle S|^{\otimes t}$. If $\epsilon=d^{((n+2)^2-t)/2}<1/2$, then $G$ is within $\epsilon$ of the identity in operator norm, the tensor-power vectors are linearly independent, every nonzero eigenvalue of $Q$ and $Q^+$ lies in $[1-2\epsilon,1+2\epsilon]$, and the vectors $(Q^+)^{1/2}|S\rangle^{\otimes t}$ are orthonormal. These conclusions are independent of representative phases.
--
--   $$
--   \|G-I\|_\infty\leq\epsilon,\qquad\operatorname{spec}_{\ne0}(Q),\operatorname{spec}_{\ne0}(Q^+)\subseteq[1-2\epsilon,1+2\epsilon].
--   $$
--
--   This gives the source's near orthogonality of stabilizer tensor powers in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 53, lemma-7.1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF pp.53--54, Lemma 7.1: constructed Gram/frame operators, nonzero spectra, and orthonormalization. -/
theorem stabilizerGramEstimate (d n t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (hn : 1 ≤ n) (ht : 1 ≤ t)
    (he : Real.rpow (d : ℝ) ((((n : ℝ) + 2) ^ 2 - t) / 2) < 1 / 2) :
    let epsilon := Real.rpow (d : ℝ) ((((n : ℝ) + 2) ^ 2 - t) / 2)
    let Q := stabilizerFrame d n t
    let P := positivePseudoInverse Q
    QAlgorithms.specNorm (stabilizerGram d n t - 1) ≤ epsilon ∧
    LinearIndependent ℂ (fun S : {S // S ∈ stabilizers d n} => QAlgorithms.tensorPow t (stabilizerVector S.val)) ∧
    (∀ k, QAlgorithms.ascEigenvalues Q k ≠ 0 →
      QAlgorithms.ascEigenvalues Q k ∈ Set.Icc (1 - 2 * epsilon) (1 + 2 * epsilon)) ∧
    (∀ k, QAlgorithms.ascEigenvalues P k ≠ 0 →
      QAlgorithms.ascEigenvalues P k ∈ Set.Icc (1 - 2 * epsilon) (1 + 2 * epsilon)) ∧
    Orthonormal ℂ (fun S : {S // S ∈ stabilizers d n} =>
      QAlgorithms.act (cfc Real.sqrt P) (QAlgorithms.tensorPow t (stabilizerVector S.val))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
