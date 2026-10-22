-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_majority_three_algorithm
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.majority_three_algorithm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:38:56.045437+00:00
-- url     : https://prove2.me/theorems/84f302b7-e943-4eaa-ae71-c71a49ed776c
-- title:
--   §3.5: explicit three-input majority algorithm
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   For $n=3$, the template with both parameters equal to one is a channel with worst-case fidelity $8/9$. Its outputs on weights zero and one, in basis $U$, are respectively
--   $$U|0\rangle\langle0|U^\dagger,\qquad U\bigl(\tfrac89|0\rangle\langle0|+\tfrac19|1\rangle\langle1|\bigr)U^\dagger.$$
--   The probabilities of $k=1,0$ are $0,1$ at weight zero and $2/3,1/3$ at weight one. The source branch outputs are also retained explicitly as unnormalized operators: the degree-one branch is absent at weight zero and gives the target at weight one; the degree-three branch gives the target at weight zero and the mixture with populations $2/3,1/3$ at weight one, each multiplied by its stated branch probability.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 25, §3.5: explicit three-input majority algorithm

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.25-26, (3.46): exact attained three-input construction, including
its two output densities and all four branch weights. -/
theorem majority_three_algorithm (alpha : RealSchurCoefficients 3) (ha : LawfulCoefficients alpha) :
    IsChannel (template alpha (fun _ => 1)) ∧
    functionFidelity (fun _ => True) (majority 3) (template alpha (fun _ => 1)) = 8/9 ∧
    (∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      template alpha (fun _ => 1) (encodedInput U.val (weightRepresentative 3 0)) = targetDensity U.val 0 ∧
      template alpha (fun _ => 1) (encodedInput U.val (weightRepresentative 3 1)) =
        (8/9 : ℂ) • targetDensity U.val 0 + (1/9 : ℂ) • targetDensity U.val 1 ∧
      preprocessingBranch alpha ⟨1, by norm_num⟩ (encodedInput U.val (weightRepresentative 3 0)) = 0 ∧
      partialTraceChannel 3 (preprocessingBranch alpha ⟨0, by norm_num⟩
        (encodedInput U.val (weightRepresentative 3 0))) = targetDensity U.val 0 ∧
      partialTraceChannel 1 (preprocessingBranch alpha ⟨1, by norm_num⟩
        (encodedInput U.val (weightRepresentative 3 1))) = (2/3 : ℂ) • targetDensity U.val 0 ∧
      partialTraceChannel 3 (preprocessingBranch alpha ⟨0, by norm_num⟩
        (encodedInput U.val (weightRepresentative 3 1))) =
          (1/3 : ℂ) • ((2/3 : ℂ) • targetDensity U.val 0 + (1/3 : ℂ) • targetDensity U.val 1)) ∧
    samplingProbability 3 0 ⟨1, by norm_num⟩ = 0 ∧
    samplingProbability 3 0 ⟨0, by norm_num⟩ = 1 ∧
    samplingProbability 3 1 ⟨1, by norm_num⟩ = 2/3 ∧
    samplingProbability 3 1 ⟨0, by norm_num⟩ = 1/3 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
