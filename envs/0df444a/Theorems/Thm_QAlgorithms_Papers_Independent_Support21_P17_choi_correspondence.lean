-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_choi_correspondence
-- name    : QAlgorithms.Papers.Independent.Support21.P17.choi_correspondence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:48:00.513116+00:00
-- url     : https://prove2.me/theorems/0ac06b0b-486f-4a64-b2f5-5debc034f223
-- title:
--   Full CP–positive-operator correspondence
-- statement:
--   Fix positive integers $m,n$ and orthonormal bases of $\mathbb C^m$ and $\mathbb C^n$. For a complex-linear map $T:M_m\to M_n$, define the output-first coordinate $F_T$ by $(F_T)_{\mu i,\nu j}=m[T(E_{ij})]_{\mu\nu}$. Then $T$ is CP if and only if $F_T\ge0$, and these assignments are mutually inverse:
--
--   $$T(A)=\frac1m\operatorname{Tr}_{\mathbb C^m}[(I_n\otimes A^{\mathsf T})F_T],\qquad F_{T_F}=F,\qquad T_{F_T}=T.$$
--
--   The constructed tracial dilation $V_{m,n}$ also gives $T(A)=V_{m,n}^*(A\otimes F_T)V_{m,n}$. For CP $T$, it is a quantum operation precisely when $\operatorname{Tr}_{\mathbb C^m}F_T\le mI_n$; in that case $F_T\le m^2I$ and $T\le m^2\Phi_{m,n}$, where $\Phi_{m,n}(A)=\operatorname{Tr}(A)I_n/m$. Thus the full bijection is retained while the uniform bound is restricted to operations. All finite-dimensional linear maps are normal.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 14, §5 and §5.1, unnumbered: full CP–positive-operator correspondence

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- Section 5.1, PDF pp.14–15: the full CP/positive-operator bijection, its inverse,
operation normalization, and the m^2 bound restricted to operations. All linear maps
are normal in this finite-dimensional setting. The unrestricted printed bound in
Theorem 5.1 is separately deferred, rather than imported into this correspondence. -/
theorem choi_correspondence (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∀ T : Lin m n,
      Entanglement.IsCompletelyPositive T ↔ (scaledChoi T).PosSemidef) ∧
    (∀ T : Lin m n, fromScaledChoi (scaledChoi T) = T) ∧
    (∀ F : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ,
      scaledChoi (fromScaledChoi F) = F ∧
      (F.PosSemidef → Entanglement.IsCompletelyPositive (fromScaledChoi F))) ∧
    (∀ (T : Lin m n), Entanglement.IsCompletelyPositive T →
      (∀ A, T A = (tracialV m n).conjTranspose * Matrix.kronecker A (scaledChoi T) * tracialV m n) ∧
      (∀ A, T A = (m : ℂ)⁻¹ • traceRight
        (Matrix.kronecker (1 : M n) A.transpose * scaledChoi T)) ∧
      ((1 - T 1).PosSemidef ↔ ((m : ℂ) • (1 : M n) - traceRight (scaledChoi T)).PosSemidef) ∧
      ((1 - T 1).PosSemidef →
        (((m : ℂ) ^ 2) • (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) - scaledChoi T).PosSemidef ∧
        Entanglement.IsCompletelyPositive (((m : ℂ) ^ 2) • tracialPreparation m n - T))) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
