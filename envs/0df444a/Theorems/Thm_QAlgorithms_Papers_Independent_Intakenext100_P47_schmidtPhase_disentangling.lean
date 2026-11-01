-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_schmidtPhase_disentangling
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.schmidtPhase_disentangling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:20:30.459998+00:00
-- url     : https://prove2.me/theorems/7e2da731-9419-4914-a963-15d020432a21
-- title:
--   Section III.C: Schmidt phase randomization and the attained classical correlation
-- statement:
--   Let $A,B$ be finite nonzero complex spaces and let $D\ge1$. Let $a_j\in A$ and $b_j\in B$ be orthonormal families indexed by $j=0,\ldots,D-1$, and let $f_j>0$, $\sum_j f_j=1$. Put $|\Phi\rangle=\sum_j\sqrt{f_j}|a_jb_j\rangle$ and define $U_k a_j=e^{2\pi\mathrm{i}kj/D}a_j$, extending $U_k$ by the identity on the unused orthogonal complement. The $D$-term uniform Alice-only ensemble has output
--
--   $$\frac1D\sum_{k=0}^{D-1}(U_k\otimes\mathbf1)|\Phi\rangle\langle\Phi|(U_k\otimes\mathbf1)^\dagger=\sigma:=\sum_jf_j|a_jb_j\rangle\langle a_jb_j|.$$
--
--   This is a separable density matrix and its attained classical mutual information is
--
--   $$I(A:B)_\sigma=H(f)=S(\Phi_A).$$
--
--   The construction supplies an explicit finite disentangling map, including unequal ambient dimensions and $D=1$. It makes no optimality assertion over general local operations.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 8, Section III.C: Schmidt phase randomization and the attained classical correlation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P47

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies localProduct)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon Config)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, III.C: D equiprobable phase unitaries, separability, and the attained classical bit entropy.
The index range 0,...,D-1 is the same root-of-unity ensemble as the printed 1,...,D. -/
theorem schmidtPhase_disentangling {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (D : ℕ) (hD : 0 < D) (f : Fin D → ℝ)
    (hf : ∀ j, 0 < f j) (hsum : ∑ j, f j = 1)
    (a : Matrix A (Fin D) ℂ) (b : Matrix B (Fin D) ℂ)
    (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) :
    ∃ R : COLUR A B, ∃ e : Fin R.count ≃ Fin D,
      R.count = D ∧ (∀ i, R.weight i = (D : ℝ)⁻¹) ∧ R.allowed .alice ∧
      (∀ i, (R.alice i : Matrix A A ℂ) = schmidtPhase a (e i)) ∧
      R.operation (pureDensity (schmidtKet f a b)) = schmidtDiagonal f a b ∧
      Entanglement.IsSeparableDensity (schmidtDiagonal f a b) ∧
      mutualInformation (schmidtDiagonal f a b) = shannon f ∧
      shannon f = vnEntropy (traceRight (pureDensity (schmidtKet f a b))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
