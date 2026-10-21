-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_faithful_state_coordinates
-- name    : QAlgorithms.Papers.Independent.Support21.P17.faithful_state_coordinates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:51:29.883949+00:00
-- url     : https://prove2.me/theorems/ec0c2e92-8d2e-4533-899c-3b0773dd1cb3
-- title:
--   Finite faithful-state RN coordinates
-- statement:
--   Let $m,n>0$ and let a faithful state on $M_m$ have density $D=\operatorname{diag}(p_i)$ in a fixed orthonormal basis, with $p_i>0$ and $\sum_i p_i=1$. Put $\Phi_\omega(A)=\operatorname{Tr}(DA)I_n$, and let $T:M_m\to M_n$ be any CP map. Define $F_{T,\omega}$ by entries $[F_{T,\omega}]_{\mu i,\nu j}=(p_ip_j)^{-1/2}[T(E_{ij})]_{\mu\nu}$. Then $F_{T,\omega}\ge0$ and
--
--   $$T(A)=V_\omega^*(A\otimes F_{T,\omega})V_\omega,\quad T\le\|F_{T,\omega}\|\Phi_\omega,\quad\|F_{T,\omega}\|\le\|D^{-1}\|^2\|T\|_{\rm cb}.$$
--
--   Here $(V_\omega)_{i,\mu j;\nu}=\sqrt{p_i}\delta_{ij}\delta_{\mu\nu}$. This coefficient operator is unique among all bounded coefficient matrices giving the compression, and some strictly positive $c$ satisfies $T\le c\Phi_\omega$, including when $T=0$. This is the faithful-state counterpart of the tracial coordinates, without subunitality.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 16, §5.2, unnumbered: finite faithful-state RN coordinates

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

/-- Section 5.2, PDF pp.16–17: every CP map has finite faithful-state RN coordinates,
a positive domination constant, the displayed norm bound, reconstruction and uniqueness.
T=0 is allowed; c is still strictly positive. The density inverse is finite-dimensional. -/
theorem faithful_state_coordinates (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (T : Lin m n) (hT : Entanglement.IsCompletelyPositive T) :
    (faithfulChoi p T).PosSemidef ∧
    (∃ c : ℝ, 0 < c ∧ Entanglement.IsCompletelyPositive
      ((c : ℂ) • faithfulPreparation n p - T)) ∧
    specNorm (faithfulChoi p T) ≤ specNorm (densityInverse p) ^ 2 * matrixCBNorm T ∧
    Entanglement.IsCompletelyPositive
      ((specNorm (faithfulChoi p T) : ℂ) • faithfulPreparation n p - T) ∧
    (∀ A, T A = (faithfulV n p).conjTranspose * Matrix.kronecker A (faithfulChoi p T) * faithfulV n p) ∧
    (∀ F : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ,
      (∀ A, T A = (faithfulV n p).conjTranspose * Matrix.kronecker A F * faithfulV n p) →
      F = faithfulChoi p T) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
