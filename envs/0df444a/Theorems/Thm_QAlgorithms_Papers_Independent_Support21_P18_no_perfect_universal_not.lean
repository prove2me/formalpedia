-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_no_perfect_universal_not
-- name    : QAlgorithms.Papers.Independent.Support21.P18.no_perfect_universal_not
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:47:24.285214+00:00
-- url     : https://prove2.me/theorems/456a7909-50b5-4659-bb51-345535f5f8a2
-- title:
--   No perfect universal one-qubit NOT
-- statement:
--   Let $\mathcal H=\mathbb C^2$. A physical gate is a completely positive trace-preserving map on all operators, including those representing parts of entangled states. There is no such qubit-to-qubit map satisfying
--   $$
--   T(|\psi\rangle\langle\psi|)=I-|\psi\rangle\langle\psi|\qquad\text{for every unit }\psi\in\mathcal H.
--   $$
--   The right side is the orthogonal pure-state complement. This excludes a perfect input-independent physical universal NOT, including any realization with a fixed ancillary state.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 1, Introduction, Eq.(1): impossibility of a perfect universal one-qubit NOT

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.1, discussion following Eq.(1): an ideal one-input universal NOT is
impossible as a physical CPTP gate, even allowing input-independent ancillas. -/
theorem no_perfect_universal_not :
    ¬ ∃ T : Superop (Fin 2) (Fin 2), IsChannel T ∧
      ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
        T (pureDensity psi) = orthogonalDensity psi := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
