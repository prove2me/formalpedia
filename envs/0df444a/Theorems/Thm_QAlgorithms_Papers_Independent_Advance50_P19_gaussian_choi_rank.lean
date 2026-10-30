-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_gaussian_choi_rank
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.gaussian_choi_rank
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:02:39.656152+00:00
-- url     : https://prove2.me/theorems/6445da05-7fa1-4741-9703-2b9e4805310b
-- title:
--   Gaussian Choi rank and kernel dimensions
-- statement:
--   Let $T$ be an $n\to n$ fermionic Gaussian CPTP channel with parameters $A,B$. Construct its normalized ordinary Choi density $J(T)$ from the actual channel and write $r=\log_2\operatorname{rank}J(T)$ for its rank in modes. Set $M=\begin{pmatrix}B&A\\-A^T&0\end{pmatrix}$ and $\ell=\dim_{\mathbb C}\ker(I-AA^T-iB)$. Then
--
--   $$\operatorname{rank}J(T)=2^r,\qquad r=2n-\ell,\qquad\dim_{\mathbb C}\ker(I-iM)=\ell,$$
--
--   and $2r$ is the number of eigenvalues of $M$ with modulus strictly below one, counted with multiplicity. If $I-AA^T$ has full rank and $B'=(I-AA^T)^{-1/2}B(I-AA^T)^{-1/2}$, then also $\ell=\dim_{\mathbb C}\ker(I-iB')$. This identifies the required environment size without defining it by the formula to be proved.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 9, Lemma S9

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, Lemma S9: ordinary Choi rank is 2^r and its mode rank r is
2n-l. Eigenvalues are counted with algebraic multiplicity, using the complex
characteristic polynomial of M. The final normalized-noise equality is guarded
by full rank of I-AA^T. The proof's mixed-mode kernel-dimension typo is not used. -/
theorem gaussian_choi_rank {n : ℕ} (s t : CARSystem n)
    (T : Superop (Qubits n) (Qubits n)) (A B : Matrix (Major n) (Major n) ℝ)
    (hT : IsFGC s t T A B) :
    let M := (choiCovariance A B).map Complex.ofReal
    let l := nullityC (fermionicCPMatrix A B)
    let r := choiModeRank T
    Matrix.rank (normalizedChoiDensity T) = 2 ^ r ∧
      r = 2 * n - l ∧
      nullityC (1 - Complex.I • M) = l ∧
      2 * r = (M.charpoly.roots.filter (fun z => ‖z‖ < 1)).card ∧
      (Matrix.rank (1 - A * A.transpose) = 2 * n →
        l = nullityC (1 - Complex.I • normalizedNoise A B)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
