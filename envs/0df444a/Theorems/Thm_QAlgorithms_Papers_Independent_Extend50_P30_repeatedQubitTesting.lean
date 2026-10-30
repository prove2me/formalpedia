-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_repeatedQubitTesting
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.repeatedQubitTesting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:57:37.588449+00:00
-- url     : https://prove2.me/theorems/74f7e302-0b5d-4723-9d76-519da34cbe37
-- title:
--   Dimension-independent repeated qubit test
-- statement:
--   There is an absolute $C>0$ such that for every number $n$ of qubits and every $\varepsilon>0$, there is one binary test, fixed before the unknown input $\psi$, using $k=6r$ copies. Its effect is the tensor product of $r$ independent Algorithm 1 effects. It accepts every stabilizer with probability one and accepts any normalized state with all stabilizer fidelities at most $1-\varepsilon^2$ with probability at most $1/3$. Zero repetitions are allowed for an empty far-state promise.
--
--   $$
--   k=6r\leq\frac{C}{\varepsilon^2},\qquad p_{\rm reject}(\psi)\geq\frac23.
--   $$
--
--   This gives the source's dimension-independent repeated qubit test in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 22, corollary-3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.22, Corollary 3.4: a universal copy bound, with repetitions tied to the physical effect. -/
theorem repeatedQubitTesting :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ r : ℕ, ∃ A : CopyTest 2 n,
        A.copies = 6 * r ∧ HEq A.accept (repeatEffect r (qubitTest n)) ∧
        (A.copies : ℝ) ≤ C / epsilon ^ 2 ∧
        ∀ v : EuclideanSpace ℂ (ResidueRegister 2 n), ‖v‖ = 1 →
          (IsStabilizer v → A.prob v = 1) ∧
          (FarFromStabilizers v epsilon → A.prob v ≤ 1 / 3) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
