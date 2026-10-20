-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_completeTester_characterization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.completeTester_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:44:58.210344+00:00
-- url     : https://prove2.me/theorems/225dad41-c0bc-4379-be59-ef9f427cf411
-- title:
--   Theorem 15: characterization of complete testers
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $\{P_i\}$ be an $N$-tester, $N\ge1$. It is informationally complete if and only if there exist an invertible positive $\Theta$ satisfying the full tester normalization and an informationally complete POVM $\{E_i\}$ such that
--
--   $$
--   P_i=(I\otimes\sqrt\Theta)E_i(I\otimes\sqrt\Theta)\quad\text{for every }i.
--   $$
--
--   The positive square root is defined by spectral calculus. All effects share the same normalization operator.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 20, Theorem 15: characterization of complete testers

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.20, Theorem 15: complete testers are exactly invertible normalized sandwiches
of complete POVMs. The roots are retained from the theorem, not the swapped converse line. -/
theorem completeTester_characterization (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ)
    (hP : CombTester s (n+1) k P) :
    InformationallyComplete P ↔
      ∃ T : Matrix (Fin (s.input n) × Basis s n) _ ℂ,
        ThetaNormalized s n T ∧ IsUnit T ∧
        ∃ E : Fin k → Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ,
          POVM E ∧ InformationallyComplete E ∧
          let A : Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ :=
            Matrix.kronecker
              (1 : Matrix (Fin (s.output n)) (Fin (s.output n)) ℂ) (matrixSqrt T)
          ∀ i, P i = A * E i * A := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
