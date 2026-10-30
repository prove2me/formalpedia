-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_block_positivity
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.block_positivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:56:38.150564+00:00
-- url     : https://prove2.me/theorems/5e4dca35-ce48-4414-b7eb-e87413e002ba
-- title:
--   Corrected singular Schur criterion and realification
-- statement:
--   Let $X$ and $Z$ be Hermitian matrices on finite-dimensional complex spaces and let $Y$ be a rectangular matrix between the corresponding spaces. Let $Z^+$ be the spectral Moore–Penrose inverse, equal to zero on the kernel. Then the corrected singular Schur criterion is
--
--   $$\begin{pmatrix}X&Y\\Y^\dagger&Z\end{pmatrix}\succeq0\iff Z\succeq0,\quad\ker Z\subseteq\ker Y,\quad X-YZ^+Y^\dagger\succeq0.$$
--
--   If $X_0$ is real symmetric and $Y_0$ is real skew symmetric of the same size, then also
--
--   $$\begin{pmatrix}X_0&Y_0\\Y_0^T&X_0\end{pmatrix}\succeq0\iff X_0+iY_0\succeq0.$$
--
--   These criteria apply to singular blocks. The first equivalence corrects the printed omission of $Z\succeq0$, which the source's proof uses.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 6, Lemma S1(i,ii)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Lemma S1(i,ii). SOURCE CORRECTION C1: the printed RHS of
(i) omits Z >= 0; it is included here because the proof uses it and the printed
version fails at X=1,Y=0,Z=-1. The inverse is spectral Moore--Penrose, including
zero eigenvalues. In (ii), Xr is symmetric and Yr is skew symmetric. -/
theorem block_positivity {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (X : Matrix I I ℂ) (Y : Matrix I J ℂ) (Z : Matrix J J ℂ)
    (hX : X.IsHermitian) (hZ : Z.IsHermitian)
    (Xr Yr : Matrix K K ℝ) (hXr : Xr.transpose = Xr) (hYr : Yr.transpose = -Yr) :
    ((Matrix.fromBlocks X Y Y.conjTranspose Z).PosSemidef ↔
      Z.PosSemidef ∧
      (∀ v : J → ℂ, Z.mulVec v = 0 → Y.mulVec v = 0) ∧
      (X - Y * cfc (fun x : ℝ => x⁻¹) Z * Y.conjTranspose).PosSemidef) ∧
    (((Matrix.fromBlocks Xr Yr Yr.transpose Xr).map Complex.ofReal).PosSemidef ↔
      (Xr.map Complex.ofReal + Complex.I • Yr.map Complex.ofReal).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
