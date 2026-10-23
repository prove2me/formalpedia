-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P38_timeReversalCosts
-- name    : QAlgorithms.Papers.Independent.Gap48.P38.timeReversalCosts
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:10:38.02318+00:00
-- url     : https://prove2.me/theorems/5cfc1d2b-dda0-4bcd-b80c-1e9e20a3b9de
-- title:
--   §I/§V, unnumbered: symmetry of optimal costs
-- statement:
--   Let $|\psi\rangle^{ABCD}$ be a unit vector on nonempty finite complex registers. All entropies refer to its actual reduced density matrices and are measured in bits. Define the forward corner expressions by $Q_\to^*=I(C;D\mid B)/2$ and $E_\to^*=[I(A;C)-I(B;C)]/2$, and define the reverse expressions by exchanging the sender and receiver side information: $Q_\leftarrow^*=I(C;D\mid A)/2$ and $E_\leftarrow^*=[I(B;C)-I(A;C)]/2$. Then
--
--   $$I(C;D\mid A)=I(C;D\mid B),\qquad Q_\leftarrow^*=Q_\to^*,\qquad E_\leftarrow^*=-E_\to^*.$$
--
--   These are the explicitly stated symmetry relations for the corner values in equation (2). No additional claim that the finite protocol consists of globally dimension-preserving isometries is included.
-- source:
--   Optimal quantum source coding with quantum information at the encoder and decoder, arXiv:0706.2907v2, PDF p. 2, §I/§V, unnumbered: symmetry of optimal costs

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap48.P38

/-- Sections I/V, PDF pp.2,9--10: the explicitly stated entropy identity,
symmetry of the corner qubit expression, and antisymmetry of the signed ebit
expression. No globally dimension-preserving protocol implementation is inferred. -/
theorem timeReversalCosts
    (I : Fin 4 → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (psi : EuclideanSpace ℂ (∀ i, I i)) (hpsi : ‖psi‖ = 1) :
    let rho := pureDensity psi
    registerCMI I rho {2} {3} {0} = registerCMI I rho {2} {3} {1} ∧
    registerCMI I rho {2} {3} {0} / 2 = cornerQ I rho ∧
    registerMutualInfo I rho {1} {2} / 2 - registerMutualInfo I rho {0} {2} / 2 =
      -cornerE I rho := by sorry

end QAlgorithms.Papers.Independent.Gap48.P38

end
