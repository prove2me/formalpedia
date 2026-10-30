-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_diagonal_energy_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.diagonal_energy_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:17:00.53506+00:00
-- url     : https://prove2.me/theorems/60a99907-e116-4921-a7d2-2cd0a28fde14
-- title:
--   Lemma 8: the full product-energy diagonal expansion
-- statement:
--   Let n,d≥1 and let H be Hermitian and diagonal in the product basis of n d-level systems. For 1≤l<d put Z^{(l)}=|l-1⟩⟨l-1|-|l⟩⟨l|. There are real diagonal entries h_x and real coefficients c_a indexed by patterns a that choose I or one Z^{(l)} at each site, such that
--
--   $$H=\sum_x h_x|x\rangle\langle x|=\frac{\operatorname{Tr}H}{d^n}I+\sum_{a\ne(I,\ldots,I)}c_a\bigotimes_j a_j.$$
--
--   This is the source expansion with each selected site and nonzero level counted once. For d=1 the nonidentity sum is empty.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 48, Lemma 8: the full product-energy diagonal expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.48, Lemma 8/G39–G40: the full physical product-energy expansion.
Positive d makes Tr(I)=d^n nonzero; d=1 leaves only the scalar term. -/
theorem diagonal_energy_expansion (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (H : EMat n d) (hH : H.IsHermitian) (hDiag : Matrix.IsDiag H) :
    (∃ h : EnergyBasis n d → ℝ, H = Matrix.diagonal (fun x => (h x : ℂ))) ∧
    ∃ c : (Fin n → Option (Fin (d-1))) → ℝ,
      H = (Matrix.trace H / (d : ℂ)^n) • (1 : EMat n d) +
        ∑ a ∈ Finset.univ.filter (fun a => ∃ j, a j ≠ none),
          (c a : ℂ) • energyDiagonalMonomial n d a := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
