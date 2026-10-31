-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_localInversionGradient
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.localInversionGradient
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:58:19.077325+00:00
-- url     : https://prove2.me/theorems/2f72d9ca-ab25-4f4b-b7c4-1a7443f9eacb
-- title:
--   The local inversion gradient by directional differentiation
-- statement:
--   Let $n\ge1$, let $H$ be Hermitian and traceless, and use the real Hilbert–Schmidt metric $\langle A,B\rangle=\operatorname{Re}\operatorname{tr}(A^\dagger B)$. Let $\mathfrak k$ be the real span of the embedded skew Pauli generators, and let $P_{\mathfrak k}$ be their orthogonal projection, with normalization $2^{-n}$. This projection belongs to $\mathfrak k$ and leaves an orthogonal residual. For $f(K)=-\operatorname{Re}\operatorname{tr}(KHK^\dagger H)$ and every $\Omega\in\mathfrak k$,
--
--   $$\left.\frac{d}{ds}f(e^{s\Omega}K)\right|_{s=0}=\left\langle P_{\mathfrak k}([KHK^\dagger,H]),\Omega\right\rangle.$$
--
--   Thus the gradient field is $P_{\mathfrak k}([KHK^\dagger,H])K$. A vanishing full commutator makes this field zero. If $KHK^\dagger=H$, it is a stationary global minimum of $f$; if $KHK^\dagger=-H$, it is a stationary global maximum. No convergence or global numerical-search guarantee is included.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 11, (65)–(67): local gradient field for type-I inversion

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- (65)–(67), PDF pp.11–12: the gradient is specified by its actual
real directional derivative in every local skew direction. No step-size,
convergence, or global-search guarantee is asserted. -/
theorem localInversionGradient {n : ℕ} (hn : 0 < n)
    (H : Op (QAlgorithms.Qubits n)) (hH : IsHamiltonian H) :
    (∀ A : Op (QAlgorithms.Qubits n), toLocalIndex (localSkewProjection A) ∈
      QAlgorithms.Papers.Independent.Advance50.P38.localAlgebra n ∧
      ∀ Omega : Op (QAlgorithms.Qubits n), toLocalIndex Omega ∈ QAlgorithms.Papers.Independent.Advance50.P38.localAlgebra n →
        realHSPairing (A - localSkewProjection A) Omega = 0) ∧
    (∀ (K : LocalSU n) (Omega : Op (QAlgorithms.Qubits n)), toLocalIndex Omega ∈ QAlgorithms.Papers.Independent.Advance50.P38.localAlgebra n →
      HasDerivAt (fun s : ℝ => reversalOverlap H
        (NormedSpace.exp (s • Omega) * localMatrix K))
        (realHSPairing (localSkewProjection (comm (localAd K H) H)) Omega) 0) ∧
    (∀ K : LocalSU n, comm (localAd K H) H = 0 →
      localSkewProjection (comm (localAd K H) H) * localMatrix K = 0) ∧
    (∀ K : LocalSU n,
      (localAd K H = H →
        localSkewProjection (comm (localAd K H) H) * localMatrix K = 0 ∧
        ∀ L : LocalSU n, reversalOverlap H (localMatrix K) ≤
          reversalOverlap H (localMatrix L)) ∧
      (localAd K H = -H →
        localSkewProjection (comm (localAd K H) H) * localMatrix K = 0 ∧
        ∀ L : LocalSU n, reversalOverlap H (localMatrix L) ≤
          reversalOverlap H (localMatrix K))) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
