-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_perfectly_transmitted_modes
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.perfectly_transmitted_modes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:01:49.347026+00:00
-- url     : https://prove2.me/theorems/35bcb6b7-2747-47d9-8a25-b9e024408c72
-- title:
--   Factor off perfectly transmitted Majorana pairs
-- statement:
--   Let $T$ be an $n\to m$ fermionic Gaussian CPTP channel with parameters $A,B$. Suppose at least $k$ singular values of $A$ equal one and $2\ell\le k$. There are actual Gaussian, possibly parity-normalizing, input and output unitaries with orthogonal phase matrices $R,Q$ such that, in the resulting coordinates,
--
--   $$QAR=I_{2\ell}\oplus A',\qquad QBQ^T=0_{2\ell}\oplus B'.$$
--
--   All cross blocks involving the first $2\ell$ directions vanish. Thus the corresponding $\ell$ full fermionic modes are an independent identity factor. The admissible bound is $\ell\le\lfloor k/2\rfloor$; noise vanishing is a conclusion of complete positivity.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 9, Lemma S8

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, Lemma S8: at least k perfectly transmitted Majorana directions
allow any l full pairs (2l <= k) to be factored off. The transformed A is identity
on those directions with zero cross blocks; transformed B vanishes there as a
CONCLUSION. The remaining block is exactly the source's independent FGC factor. -/
theorem perfectly_transmitted_modes {n m k l : ℕ} (s : CARSystem n)
    (t : CARSystem m) (T : Superop (Qubits n) (Qubits m))
    (A : Matrix (Major m) (Major n) ℝ) (B : Matrix (Major m) (Major m) ℝ)
    (hT : IsFGC s t T A B) (hl : 2 * l ≤ k)
    (hk : k ≤ nullityR (1 - A * A.transpose)) :
    l ≤ n ∧ l ≤ m ∧
    ∃ (Q : Matrix (Major m) (Major m) ℝ) (R : Matrix (Major n) (Major n) ℝ)
      (U : Matrix.unitaryGroup (Qubits m) ℂ) (V : Matrix.unitaryGroup (Qubits n) ℂ),
      ImplementsCAR t Q U ∧ ImplementsCAR s R V ∧
      (∀ (i : Major m) (j : Major n), i.val < 2 * l ∨ j.val < 2 * l →
        (Q * A * R) i j = if i.val = j.val then 1 else 0) ∧
      (∀ i j : Major m, i.val < 2 * l ∨ j.val < 2 * l →
        (Q * B * Q.transpose) i j = 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
