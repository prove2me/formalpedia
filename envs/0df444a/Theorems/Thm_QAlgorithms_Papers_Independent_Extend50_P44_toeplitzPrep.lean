-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_toeplitzPrep
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.toeplitzPrep
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:18:31.552549+00:00
-- url     : https://prove2.me/theorems/db6aaf45-712c-4da3-91aa-8e66ecb77590
-- title:
--   §3.2: Toeplitz PREP/UNPREP circuit (56)
-- statement:
--   Let $N=2^n$, $D=2^d\le N$, $0\le k<D$, and let the nonzero real data values define the banded Toeplitz matrix $A_{ij}=a_t$ for $i-j=t-k$. Its label oracles preserve the data register and are fixed before the values. For every $p\in[0,1]$, circuit (56) is an exact block encoding with
--   $$ \alpha_p=\sqrt{\left(\sum_{t=0}^{D-1}|a_t|^{2p}\right)\left(\sum_{t=0}^{D-1}|a_t|^{2-2p}\right)}. $$
--   The circuit uses $2D$ supplied-item loads, $d+1$ flags, and the overflow deletion inherited from the Toeplitz base scheme. Here $S_c=S_r=D$, so the prefactor in (32) is one.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 15, §3.2: Toeplitz PREP/UNPREP circuit (56)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF p.15, (56): commuting Toeplitz labels allow PREP/UNPREP.
Sc=Sr=D removes the prefactor in (32); out-of-range shifts are deleted. -/
theorem toeplitzPrep (n d : ℕ) (hd : d ≤ n) (k : Fin (2 ^ d)) :
    ∃ B : Scheme n d d n, ∃ L : PrepLayout B,
      ToeplitzLabels B k ∧ L.active = Finset.univ ∧
      loadingCost (doubleLoadingSchedule (2 ^ d)) = 2 * 2 ^ d ∧
      Fintype.card (Bool × Fin (2 ^ d)) = 2 ^ (d + 1) ∧
      ∀ a : Fin (2 ^ d) → ℝ, (∀ j, a j ≠ 0) → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      ∃ P : PreparationPair L a p, B.matrix a = bandedToeplitz n d k a ∧
        QAlgorithms.IsBlockEncoding (false, 0) (L.circuit P)
          (Real.sqrt ((∑ j, supportedPower (a j) (2 * p)) *
            ∑ j, supportedPower (a j) (2 - 2 * p))) 0 (bandedToeplitz n d k a) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
