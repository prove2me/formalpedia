-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_two_extremal_channels
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.two_extremal_channels
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:39:38.80301+00:00
-- url     : https://prove2.me/theorems/950305f7-594d-4360-93d1-a78eca79ac9c
-- title:
--   Lemma 4.1.
-- statement:
--   For $\ell\ge1$, input covariance is with $T^\ell(U)$ and output covariance with $U$, for every $U\in U(2)$. The channel $\Phi_{\rm Tr}^\ell$ embeds through $V^\ell$ and keeps the first qubit; $\Phi_{\rm UNOT}^\ell$ measures the normalized coherent-state POVM and prepares the orthogonal state. Let $D_\ell$ be the explicit real dual Clebsch–Gordan matrix (C.49),(C.54). The unnormalized Choi order is output tensor input.
--
--   The covariant channels form a convex line segment with exactly two extreme points $\Phi_1^\ell,\Phi_2^\ell$, whose Choi matrices are
--   $$J_1=D_\ell^\dagger\bigl(\tfrac{\ell+1}{\ell}I_\ell\oplus0\bigr)D_\ell,\qquad J_2=D_\ell^\dagger\bigl(0\oplus\tfrac{\ell+1}{\ell+2}I_{\ell+2}\bigr)D_\ell.$$
--   Their ranks are $\ell$ and $\ell+2$, and $\ell J_1+(\ell+2)J_2=(\ell+1)I$. Every covariant channel is a convex combination of these exact endpoints.
--
--   This characterizes the physical postprocessing maps used in the template algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 27, Lemma 4.1.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.27-28, Lemma 4.1: full D-based endpoint characterization,
including the two extreme points, exact ranks and weighted identity. -/
theorem two_extremal_channels (ell : ℕ) (hell : 1 ≤ ell) :
    Convex ℝ {Phi : Superop (Fin (ell + 1)) (Fin 2) | IsChannel Phi ∧ PolynomialCovariant ell Phi} ∧
    (∀ Phi : Superop (Fin (ell + 1)) (Fin 2),
      (IsChannel Phi ∧ PolynomialCovariant ell Phi) ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ Phi = fun rho =>
        (t : ℂ) • extremalChannel ell false rho + ((1-t : ℝ) : ℂ) • extremalChannel ell true rho) ∧
    (∀ second : Bool, IsChannel (extremalChannel ell second) ∧ PolynomialCovariant ell (extremalChannel ell second) ∧
      functionOutputChoi (extremalChannel ell second) = extremalChoi ell second) ∧
    Matrix.rank (extremalChoi ell false) = ell ∧
    Matrix.rank (extremalChoi ell true) = ell + 2 ∧
    (ell : ℂ) • extremalChoi ell false + ((ell : ℂ)+2) • extremalChoi ell true =
      ((ell : ℂ)+1) • 1 ∧
    (∀ Phi : Superop (Fin (ell + 1)) (Fin 2),
      (IsChannel Phi ∧ PolynomialCovariant ell Phi ∧
        ∀ (A B : Superop (Fin (ell + 1)) (Fin 2)) (t : ℝ),
          IsChannel A → PolynomialCovariant ell A → IsChannel B → PolynomialCovariant ell B →
          0 < t → t < 1 →
          Phi = (fun rho => (t : ℂ) • A rho + ((1-t : ℝ) : ℂ) • B rho) → A = Phi ∧ B = Phi) ↔
      Phi = extremalChannel ell false ∨ Phi = extremalChannel ell true) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
