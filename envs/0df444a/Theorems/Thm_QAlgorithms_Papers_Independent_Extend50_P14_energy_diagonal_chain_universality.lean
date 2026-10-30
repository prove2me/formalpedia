-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_energy_diagonal_chain_universality
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.energy_diagonal_chain_universality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:17:36.552328+00:00
-- url     : https://prove2.me/theorems/81a09921-d564-4aff-ae57-efc8eb789618
-- title:
--   Lemma 9: diagonal controls and nearest-neighbor energy transfer
-- statement:
--   Let n,d≥1 and ΔE>0, and let H_intr be the sum of identical site Hamiltonians with levels rΔE. Let D range over all physical diagonal Hermitian controls, and R_{j,j+1}^{(l,l')} be the transfers of G10b, with 1≤j<n and 1≤l,l'<d. Then
--
--   $$\operatorname{Lie}_{\mathbb R}\{iD,\ iR_{j,j+1}^{(l,l')}\}=\{A:A^\dagger=-A,\ [A,H_{\mathrm{intr}}]=0\}.$$
--
--   The equality retains nearest-neighbor controls; at n=1 or d=1 the empty transfer family leaves the appropriate diagonal algebra.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 49, Lemma 9: diagonal controls and nearest-neighbor energy exchange generate all energy-conserving Hamiltonians

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.49–52, Lemma 9/G51–G52: nearest-neighbor energy exchange, together
with the whole diagonal algebra, generates the full skew-Hermitian commutant. -/
theorem energy_diagonal_chain_universality (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (gap : ℝ) (hGap : 0 < gap) :
    (LieSubalgebra.lieSpan ℝ (EMat n d)
      ((fun H => Complex.I • H) '' energyDiagonalControls n d) : Set (EMat n d)) =
      {A | A + Aᴴ = 0 ∧ A * intrinsicEnergy n d gap = intrinsicEnergy n d gap * A} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
