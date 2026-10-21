-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_twirling_reduction
-- name    : QAlgorithms.Papers.Independent.Support21.P18.twirling_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:52:19.728765+00:00
-- url     : https://prove2.me/theorems/c167d42f-4b27-4e98-950f-79e47368a53e
-- title:
--   Haar averaging does not increase worst-case error
-- statement:
--   Fix $N\ge1$ and any CPTP map $T$ from the symmetric $N$-qubit input space to a qubit. Let $D_N(U)$ be the occupation-coordinate restriction of $U^{\otimes N}$ and $dU$ normalized Haar measure on $U(2)$. Define
--   $$
--   T_U(\rho)=U^\dagger T(D_N(U)\rho D_N(U)^\dagger)U,
--   \qquad\widehat T(\rho)=\int T_U(\rho)\,dU.
--   $$
--   Every $T_U$ is CPTP with $\Delta(T_U)=\Delta(T)$. The integrand is integrable for every input operator; $\widehat T$ is CPTP, $(\widehat T)_U=\widehat T$ for every $U$, and
--   $$
--   \Delta(\widehat T)\le\Delta(T).
--   $$
--   For any covariant CPTP $T$, the coherent-input overlap defining its error is independent of the unit pure input.
--
--   Thus covariance is an available reduction in the optimization over all physical gates.
--
--   Here $\Delta(S)=\max_{\|\psi\|=1}\operatorname{Tr}[|\psi\rangle\langle\psi|S(|\psi^{\otimes N}\rangle\langle\psi^{\otimes N}|)]$ is the worst-case overlap with the original state, so the corresponding worst-case complement fidelity is $1-\Delta(S)$.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 4, Optimality proof, Eq.(10): averaging never increases worst-case error

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.2,4, Eq.(10): Haar averaging is a physical covariant gate and cannot
increase worst-case error. Integrability and legality are conclusions for every
CPTP competitor; neither is imposed as an extra restriction. -/
theorem twirling_reduction (N : ℕ) (hN : 1 ≤ N)
    (T : Superop (SymmetricBasis N) (Fin 2)) (hT : IsChannel T) :
    (∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      IsChannel (rotateGate N U T) ∧ notError N (rotateGate N U T) = notError N T) ∧
    (∀ rho : Matrix (SymmetricBasis N) (SymmetricBasis N) ℂ,
      Integrable (fun U => rotateGate N U T rho) (Schur.unitaryHaar 2)) ∧
    IsChannel (twirlGate N T) ∧ IsUniversallyCovariant N (twirlGate N T) ∧
    notError N (twirlGate N T) ≤ notError N T ∧
    (IsUniversallyCovariant N T → ∀ psi phi : EuclideanSpace ℂ (Fin 2),
      IsState psi → IsState phi →
      effectProb (pureDensity psi) (T (pureDensity (symmetricQubitKet N psi))) =
        effectProb (pureDensity phi) (T (pureDensity (symmetricQubitKet N phi)))) := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
