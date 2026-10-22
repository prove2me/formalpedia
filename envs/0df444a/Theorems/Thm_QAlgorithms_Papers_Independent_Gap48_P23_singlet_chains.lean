-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_singlet_chains
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.singlet_chains
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:48:26.478351+00:00
-- url     : https://prove2.me/theorems/f70d1d03-fd86-4486-ae8f-962595c30159
-- title:
--   Corollary A.4.
-- statement:
--   Let $d\ge1$. Vectorization is unnormalized: $|A\rangle=\sum_{i,j}A_{ij}|i,j\rangle$. In Appendix A only, $\langle A|=|A\rangle^T$ is bilinear, without complex conjugation. The formal tensor contractions are independent sums over the internal path indices, in their displayed order. Put $S=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and $|\Psi^-\rangle=|S\rangle/\sqrt2$.
--
--   For $k\ge0$, the even open, odd open and closed chains of the unnormalized singlet matrix give
--   $$S^{2k}=(-1)^kI,\qquad|S^{2k+1}\rangle=(-1)^k|S\rangle,\qquad\operatorname{Tr}(S^{2k+2})=2(-1)^{k+1}.$$
--   Replacing any $j$ of the ket factors by their transposes multiplies the corresponding contraction by $(-1)^j$.
--
--   This fixes the contraction and sign conventions used in the singlet-diagram analysis.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 48, Corollary A.4.

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

/-- PDF p.48, Corollary A.4: all three unnormalized singlet chains and every
allowed ket reversal; the closed contraction includes the final bra. -/
theorem singlet_chains (k : ℕ) :
    networkChain (2*k) (fun _ => singletMatrix) = singletMatrix^(2*k) ∧
    singletMatrix^(2*k) = (-1:ℂ)^k • (1 : Op (Fin 2)) ∧
    bilinearVectorize (networkChain (2*k+1) (fun _ => singletMatrix)) =
      bilinearVectorize ((-1:ℂ)^k • singletMatrix) ∧
    (networkChain (2*k+2) (fun _ => singletMatrix)).trace = 2*(-1:ℂ)^(k+1) ∧
    (∀ (extra : ℕ), extra ≤ 2 → ∀ reverse : Fin (k+1) → Bool,
      networkChain (2*k+extra) (reversedKetFactors k extra singletMatrix reverse) =
        (-1:ℂ)^(reversalCount k extra reverse) • networkChain (2*k+extra) (fun _ => singletMatrix)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
