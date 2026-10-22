-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_normalized_singlet_chains
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.normalized_singlet_chains
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:50:37.312577+00:00
-- url     : https://prove2.me/theorems/25caabe2-7311-4f54-ab9f-292c46b21822
-- title:
--   Corollary B.3.
-- statement:
--   Let $d\ge1$. Vectorization is unnormalized: $|A\rangle=\sum_{i,j}A_{ij}|i,j\rangle$. In Appendix A only, $\langle A|=|A\rangle^T$ is bilinear, without complex conjugation. The formal tensor contractions are independent sums over the internal path indices, in their displayed order. Put $S=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and $|\Psi^-\rangle=|S\rangle/\sqrt2$.
--
--   For $k\ge0$, the normalized singlet chains are
--   $$\frac{(-1)^k}{2^k}I,\qquad\frac{(-1)^k}{2^k}|\Psi^-\rangle,\qquad\frac{(-1)^{k+1}}{2^k}$$
--   for the even open, odd open and closed contractions, respectively. Reversing any $j$ ket singlets introduces the factor $(-1)^j$; the closed value at $k=0$ is $-1$.
--
--   This fixes the contraction and sign conventions used in the singlet-diagram analysis.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 51, Corollary B.3.

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

/-- PDF p.51, Corollary B.3: normalized singlet chains; at k=0 the closed
contraction is -1. All ket reversals preserve the exact sign rule. -/
theorem normalized_singlet_chains (k : ℕ) :
    networkChain (2*k) (fun _ => normalizedSingletMatrix) =
      ((-1:ℂ)^k / 2^k) • (1 : Op (Fin 2)) ∧
    bilinearVectorize (networkChain (2*k+1) (fun _ => normalizedSingletMatrix)) =
      bilinearVectorize (((-1:ℂ)^k / 2^k) • normalizedSingletMatrix) ∧
    (networkChain (2*k+2) (fun _ => normalizedSingletMatrix)).trace = (-1:ℂ)^(k+1)/2^k ∧
    (∀ (extra : ℕ), extra ≤ 2 → ∀ reverse : Fin (k+1) → Bool,
      networkChain (2*k+extra) (reversedKetFactors k extra normalizedSingletMatrix reverse) =
        (-1:ℂ)^(reversalCount k extra reverse) •
          networkChain (2*k+extra) (fun _ => normalizedSingletMatrix)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
