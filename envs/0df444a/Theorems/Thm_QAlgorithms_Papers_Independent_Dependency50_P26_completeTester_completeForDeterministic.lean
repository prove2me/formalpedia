-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_completeTester_completeForDeterministic
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.completeTester_completeForDeterministic
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:46:03.637661+00:00
-- url     : https://prove2.me/theorems/58d3d685-dd5f-4f32-be80-8feb35954798
-- title:
--   §V B: existence of testers complete for deterministic combs
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $\{P_i\}$ be an informationally complete $N$-tester, and let $D$ be the complex linear span of the deterministic $N$-combs. The tester is informationally complete on $D$:
--
--   $$
--   \forall X\in D,\quad\exists(c_i)_i,\qquad X=\sum_i c_iP_i^T.
--   $$
--
--   The true span defines $D$. No use is made of the source single-trace formula, which omits recursive constraints.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 20, §V B: existence of testers complete for deterministic combs

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.20, paragraph after Definition 14: completeness implies completeness on D. -/
theorem completeTester_completeForDeterministic (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s n) (Basis s n) ℂ)
    (hP : CombTester s n k P) (hic : InformationallyComplete P) :
    CompleteForDeterministic s n k P := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
