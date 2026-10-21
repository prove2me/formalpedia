-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_maximum_attained
-- name    : QAlgorithms.Papers.Independent.Support21.P16.maximum_attained
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:44:16.677648+00:00
-- url     : https://prove2.me/theorems/127540c6-36c7-4e35-a926-e4381329f303
-- title:
--   The optimal global fidelity has an admissible maximizer
-- statement:
--   Let $d>0$ and $1\le N<M$ be integers. An admissible map $T$ is a complex-linear completely positive trace-preserving map from the $N$-particle Bose operator algebra to the full $M$-particle algebra, canonically zero-extended. Define $\mathcal F(T)$ as the infimum, over all unit $\phi\in\mathbb C^d$, of the global overlap between $T(|\phi^{\otimes N}\rangle\langle\phi^{\otimes N}|)$ and $|\phi^{\otimes M}\rangle\langle\phi^{\otimes M}|$. Every admissible map has $0\le\mathcal F(T)\le1$. Writing $\widehat F=\sup_{S\text{ admissible}}\mathcal F(S)$, there exists an admissible $T_*$ with
--   $$
--   \mathcal F(T_*)=\widehat F,\qquad
--   \mathcal F(S)\le\mathcal F(T_*)\quad\text{for every admissible }S.
--   $$
--   This asserts an actual feasible maximum, and therefore also the nonemptiness of the admissible class, rather than merely naming a real supremum.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 9, maximum-attained

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF p.9, section 4: an admissible maximizer exists, not only a real supremum.
The feasible set is nonempty and the objective values lie in [0,1]. -/
theorem maximum_attained (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M) :
    (∀ T : CloneMap d N M, IsBoseInputChannel T → cloningFidelity T ∈ Set.Icc (0 : ℝ) 1) ∧
    ∃ T : CloneMap d N M, IsBoseInputChannel T ∧ cloningFidelity T = optimalFidelity d N M ∧
      ∀ S : CloneMap d N M, IsBoseInputChannel S → cloningFidelity S ≤ cloningFidelity T := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
