-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_completeTester_invertibleNormalization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.completeTester_invertibleNormalization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:44:20.798168+00:00
-- url     : https://prove2.me/theorems/a029c0ae-f8a4-43e3-a41a-daa81a587552
-- title:
--   Theorem 14: invertible normalization for complete testers
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $\{P_i\}$ be an informationally complete $N$-tester, $N\ge1$, and let $\Theta$ be any positive recursively normalized operator with $\sum_iP_i=I_{H_{2N-1}}\otimes\Theta$. Then
--
--   $$
--   \Theta\text{ is invertible}.
--   $$
--
--   Invertibility is represented by being a unit in the finite matrix algebra.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 20, Theorem 14: invertible normalization for complete testers

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.20, Theorem 14: any Θ providing normalization of a complete tester is invertible. -/
theorem completeTester_invertibleNormalization (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ)
    (hP : CombTester s (n+1) k P) (hic : InformationallyComplete P)
    (T : Matrix (Fin (s.input n) × Basis s n) _ ℂ)
    (hT : ThetaNormalized s n T)
    (hsum : (∑ i, P i) = Matrix.kronecker (1 : Matrix (Fin (s.output n)) _ ℂ) T) :
    IsUnit T := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
