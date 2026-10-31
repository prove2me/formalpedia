-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_frobeniusTraceCertificates
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.frobeniusTraceCertificates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:57:44.488514+00:00
-- url     : https://prove2.me/theorems/d87001a7-cfdd-4f2c-957c-6828e03ac135
-- title:
--   Attained Frobenius and trace certificates for type-I inversion
-- statement:
--   Let $n\ge1$ and let $H$ be Hermitian and traceless. For local $K$ write $D(K)=\|KHK^\dagger+H\|_F^2$ and $f(K)=-\operatorname{Re}\operatorname{tr}(KHK^\dagger H)$. Then
--
--   $$D(K)=2\|H\|_F^2-2f(K).$$
--
--   For a fixed $K$, sign reversal, zero Frobenius norm, $D(K)=0$, the trace identity $\operatorname{Re}\operatorname{tr}(HKHK^\dagger)=-\|H\|_F^2$, and reversal of $e^{-itH}$ for every real $t$ are equivalent. Under $\|H\|_F=1$, the trace identity becomes $-1$. There exist attained global minimizers $K_{\min}$ of $D$ and maximizers $K_{\max}$ of $f$, with
--
--   $$H\text{ type-I reversible}\ \Longleftrightarrow\ D(K_{\min})=0\ \Longleftrightarrow\ f(K_{\max})=\|H\|_F^2,\qquad f(K_{\max})\le\|H\|_F^2.$$
--
--   The unnormalized criteria include $H=0$ and do not rely on a possibly empty infimum.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 11, (63)–(64) and [35]: type-I Frobenius and trace certificates

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- (63)–(64), PDF pp.11–12, and footnote [35], p.19. Minima/maxima
are attained. The -1 trace test requires normalization; the unnormalized
identity and zero-distance test include H=0. -/
theorem frobeniusTraceCertificates {n : ℕ} (hn : 0 < n)
    (H : Op (QAlgorithms.Qubits n)) (hH : IsHamiltonian H) :
    (∀ K : LocalSU n,
      distanceSq H K = 2 * QAlgorithms.frobNorm H ^ 2 -
        2 * reversalOverlap H (localMatrix K)) ∧
    (∀ K : LocalSU n,
      (localAd K H = -H ↔ QAlgorithms.frobNorm (localAd K H + H) = 0) ∧
      (localAd K H = -H ↔ distanceSq H K = 0) ∧
      (localAd K H = -H ↔
        (Matrix.trace (H * localAd K H)).re = -(QAlgorithms.frobNorm H ^ 2)) ∧
      (localAd K H = -H ↔
        ∀ t : ℝ, localAd K (evolution H t) = evolution H (-t)) ∧
      (QAlgorithms.frobNorm H = 1 →
        (localAd K H = -H ↔ (Matrix.trace (H * localAd K H)).re = -1))) ∧
    (∃ Kmin : LocalSU n,
      (∀ L : LocalSU n, distanceSq H Kmin ≤ distanceSq H L) ∧
      (TypeI H ↔ distanceSq H Kmin = 0)) ∧
    (∃ Kmax : LocalSU n,
      (∀ L : LocalSU n,
        reversalOverlap H (localMatrix L) ≤ reversalOverlap H (localMatrix Kmax)) ∧
      reversalOverlap H (localMatrix Kmax) ≤ QAlgorithms.frobNorm H ^ 2 ∧
      (TypeI H ↔ reversalOverlap H (localMatrix Kmax) = QAlgorithms.frobNorm H ^ 2)) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
