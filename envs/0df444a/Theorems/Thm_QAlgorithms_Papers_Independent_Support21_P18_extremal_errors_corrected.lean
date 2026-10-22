-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_extremal_errors_corrected
-- name    : QAlgorithms.Papers.Independent.Support21.P18.extremal_errors_corrected
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:53:23.49238+00:00
-- url     : https://prove2.me/theorems/523df464-de12-4734-b592-b85f85ed7715
-- title:
--   Extremal errors with corrected spin labels
-- statement:
--   Let $N\ge1$. Let $T_-$ and $T_+$ be the channels obtained from the explicit Eq. (12) occupation-coordinate isometries, with environment spins $(N-1)/2$ and $(N+1)/2$, respectively. Then
--   $$
--   \Delta(T_-)=1,\qquad\Delta(T_+)=\frac1{N+2}.
--   $$
--   For every unit qubit vector $\psi$, with $\sigma=|\psi\rangle\langle\psi|$,
--   $$
--   T_-(\sigma^{\otimes N})=\sigma,\qquad
--   T_+(\sigma^{\otimes N})=\frac N{N+2}(I-\sigma)+\frac1{N+2}I.
--   $$
--   These are the copying and optimal complement branches.
--
--   **Formalization Note** Printed Eq. (13) assigns the two values to the opposite spins. The branch labels are corrected here: at $N=1$ the spin-zero environment makes $T_-$ the identity channel, whose error is $1$. The printed formula is retained in the verbatim field, and the correction awaits independent moderation.
--
--   Here $\Delta(S)=\max_{\|\psi\|=1}\operatorname{Tr}[|\psi\rangle\langle\psi|S(|\psi^{\otimes N}\rangle\langle\psi^{\otimes N}|)]$ is the worst-case overlap with the original state, so the corresponding worst-case complement fidelity is $1-\Delta(S)$.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 4, Optimality proof, Eq.(13): extremal error values, with corrected spin labels

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.4, Eq.(13), with corrected spin labels. PRINTED: error 1 for
j=(N+1)/2 and 1/(N+2) for j=(N-1)/2. CHANGED: these branch labels are reversed.
WHY: N=1 and j=0 in Eq.(12) gives the identity channel, whose Eq.(2) error is 1.
The unordered values and the main optimality result are preserved. Independent
moderation of this source correction is still required. -/
theorem extremal_errors_corrected (N : ℕ) (hN : 1 ≤ N) :
    notError N (lowerChannel N) = 1 ∧
    notError N (upperChannel N) = 1 / ((N : ℝ) + 2) ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
      lowerChannel N (pureDensity (symmetricQubitKet N psi)) = pureDensity psi ∧
      upperChannel N (pureDensity (symmetricQubitKet N psi)) = complementOutput N psi) := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
