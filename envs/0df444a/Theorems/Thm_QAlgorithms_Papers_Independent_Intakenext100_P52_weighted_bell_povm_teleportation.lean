-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_weighted_bell_povm_teleportation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.weighted_bell_povm_teleportation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:36:14.266251+00:00
-- url     : https://prove2.me/theorems/007eefdb-98cb-48b4-a922-f6c989862e60
-- title:
--   §2 Remark: weighted Bell POVM teleportation
-- statement:
--   Let $I$ have $d>0$ elements, let $n\ge d^2$, and let $U_i$ be unitaries with positive real weights $k_i$. Put $|\phi_i\rangle=(U_i^\dagger\otimes I)|\phi\rangle$, where $|\phi\rangle=d^{-1/2}\sum_j|j,j\rangle$, and assume the actual frame identity $\sum_i k_i|\phi_i\rangle\langle\phi_i|=I$. For any normalized input $|\alpha\rangle$, the branch obtained with bra $\sqrt{k_i}\langle\phi_i|$ is
--
--   $$ |b_i\rangle=\frac{\sqrt{k_i}}d U_i|\alpha\rangle,\qquad \Pr(i)=\frac{k_i}{d^2},\qquad \frac d{\sqrt{k_i}}U_i^\dagger|b_i\rangle=|\alpha\rangle. $$
--
--   The branch probabilities sum to one. If $n=d^2$, every $k_i=1$ and the kets $|\phi_i\rangle$ are orthonormal. This gives a physical conditional teleportation scheme under completeness, rather than an assertion that arbitrary weighted unitaries form a POVM.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 4, §2 Remark: weighted Bell POVM teleportation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Weighted Bell POVM teleportation, PDF p.4 Remark. Completeness is a genuine
frame hypothesis; no arbitrary collection of positive weights is assumed complete. -/
theorem weighted_bell_povm_teleportation {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    {n : ℕ} (U : Fin n → Matrix I I ℂ) (k : Fin n → ℝ)
    (hn : Fintype.card I ^ 2 ≤ n) (hU : ∀ i, U i ∈ Matrix.unitaryGroup I ℂ)
    (hk : ∀ i, 0 < k i) (hframe : BellFrame U k) :
    (∀ (alpha : Vec I), IsState alpha →
      (∀ i, weightedTeleport (U i) (k i) alpha =
          ((Real.sqrt (k i) : ℂ) / (Fintype.card I : ℂ)) • act (U i) alpha ∧
        ‖weightedTeleport (U i) (k i) alpha‖ ^ 2 = k i / (Fintype.card I : ℝ) ^ 2 ∧
        ((Fintype.card I : ℂ) / (Real.sqrt (k i) : ℂ)) •
          act ((U i)ᴴ) (weightedTeleport (U i) (k i) alpha) = alpha) ∧
      (∑ i, ‖weightedTeleport (U i) (k i) alpha‖ ^ 2) = 1) ∧
    (n = Fintype.card I ^ 2 → (∀ i, k i = 1) ∧
      Orthonormal ℂ (fun i => rotatedEntangledKet (U i))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
