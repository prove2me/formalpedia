-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_classical_quantum_incompatible
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.classical_quantum_incompatible
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:52:50.384136+00:00
-- url     : https://prove2.me/theorems/8b00df59-0b6a-49e2-a1c6-a36323f9de7d
-- title:
--   Proposition II.3: classical-quantum marginals may be incompatible
-- statement:
--   On two qubits define $\rho_X=(I+X\otimes X)/4$ and $\rho_Z=(I+Z\otimes Z)/4$, with $X,Z$ the Pauli matrices. Both are density operators classical on Alice in their respective $X$ and $Z$ bases, and both Alice marginals are $I/2$. Nevertheless,
--   $$\nexists\,w_{ABC}\text{ a density operator with }w_{AB}=\rho_X,\ w_{AC}=\rho_Z.$$
--   Thus classical-quantum states with consistent overlaps can be incompatible.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 4, Proposition II.3: classical-quantum marginals may be incompatible

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Proposition II.3 and its explicit witnesses, PDF p.4: different local CQ bases
are allowed; the common A marginal is completely mixed. -/
theorem classical_quantum_incompatible :
    IsDensityMatrix (cqWitness true) ∧ IsDensityMatrix (cqWitness false) ∧
    IsClassicalQuantum (cqWitness true) ∧ IsClassicalQuantum (cqWitness false) ∧
    traceRight (cqWitness true) = fullyMixed (Fin 2) ∧
    traceRight (cqWitness false) = fullyMixed (Fin 2) ∧
    ¬ JoinableTwo (cqWitness true) (cqWitness false) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
