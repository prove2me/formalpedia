-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P46_rankOne_valid_notPure
-- name    : QAlgorithms.Papers.Independent.Intake100.P46.rankOne_valid_notPure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:04:12.698261+00:00
-- url     : https://prove2.me/theorems/a7af3c55-407f-4ef5-bc57-a0cedd9dd4e2
-- title:
--   A valid rank-one process need not be reversibly pure
-- statement:
--   All systems have positive finite dimensions and fixed computational bases. Choi operators are unnormalized and input first. A valid process maps every pair of local CPTP maps, with arbitrary ancillary input and output wires, to a CPTP map. Purity tests every compatible pair of local unitaries with those same ancillary extensions.
--
--   Take $P,A_I,A_O,B_I,B_O$ one-dimensional and $F=\mathbb C^2$. Let $V$ send the unique input basis vector to $|0\rangle_F$, and put $W=|V\rangle\!\rangle\langle\!\langle V|$. Then
--
--   $$V^\dagger V=I,\qquad VV^\dagger\ne I,\qquad W\text{ is valid},\qquad \operatorname{rank}W=1,\qquad W\text{ is not pure}.$$
--
--   When both trivial laboratories apply the identity unitary, the resulting channel is $|G\rangle\!\rangle\langle\!\langle G|$ for an isometry $G:\mathbb C\to\mathbb C^2$ which is not unitary. This gives a concrete witness to the source's separating existence claim and explains why rank one does not characterize reversible purity.
-- source:
--   A purification postulate for quantum mechanics with indefinite causal order, arXiv:1611.08535v4, PDF p. 4, §2, paragraph after Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intake100.P46

/-- PDF p.4, paragraph after Theorem 2: rank-one validity does not imply reversible
purity. The displayed witness is the dimension-increasing state-output isometry. -/
theorem rankOne_valid_notPure :
    IsIsometricMatrix stateOutputIsometry ∧ ¬ IsReversibleMatrix stateOutputIsometry ∧
    IsValidProcess (processProjector (d := stateOutputSignature) stateOutputIsometry) ∧
    Matrix.rank (processProjector (d := stateOutputSignature) stateOutputIsometry) = 1 ∧
    ¬ IsPureProcess (processProjector (d := stateOutputSignature) stateOutputIsometry) ∧
    ∃ G : Matrix
      (Fin (stateOutputSignature 5 : ℕ) × Fin 1 × Fin 1)
      (Fin (stateOutputSignature 0 : ℕ) × Fin 1 × Fin 1) ℂ,
      IsIsometricMatrix G ∧ ¬ IsReversibleMatrix G ∧
      linkLaboratories stateOutputSignature 1 1 1 1 (processProjector (d := stateOutputSignature) stateOutputIsometry)
        (unitaryChannelProjector (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ))
        (unitaryChannelProjector (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)) = unitaryChannelProjector G := by sorry

end QAlgorithms.Papers.Independent.Intake100.P46

end
