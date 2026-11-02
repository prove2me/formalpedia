-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_arbitrary_block_entropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.arbitrary_block_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:09:57.186176+00:00
-- url     : https://prove2.me/theorems/4f2493a4-004e-489b-bc68-f91d591c9413
-- title:
--   Main properties (i): arbitrary block entropy, including maximal volume law
-- statement:
--   Let $N\ge1$, $0\le L\le N$, and let $h$ be any real number satisfying $0\le h\le\min(L,N-L)$. There exist bond-one RAGE data with nonzero raw vector $v$ such that $v/\|v\|$ is a pure state and its reduced density matrix $\rho_L$ on the first $L$ sites satisfies
--
--   $$S(\rho_L)=-\operatorname{tr}(\rho_L\log_2\rho_L)=h.$$
--
--   Thus every admissible entropy value, including the maximal value $\min(L,N-L)$ bits, occurs within this family. Empty and whole-chain blocks have entropy zero. For $L\le N/2$, the maximal entropy is exactly $L$ bits, giving a volume law. The entropy unit is bits, with $0\log_2 0=0$.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 1, Main properties (i): arbitrary block entropy, including maximal volume law

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- Abstract p.1 and Main properties (i), p.2: all entropy values up to the maximal
bipartite value occur already at D=1. Entropy is measured in bits. -/
theorem arbitrary_block_entropy (N L : ℕ) (hN : 1 ≤ N) (hL : L ≤ N)
    (h : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ (min L (N - L) : ℕ)) :
    ∃ (A : Tensors N 1) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ),
      rage A G V ≠ 0 ∧ IsState (normalizeRageVector (rage A G V)) ∧
      IsDensityMatrix (rageMarginal (rage A G V) (firstBlock N L)) ∧
      vnEntropy (rageMarginal (rage A G V) (firstBlock N L)) = h := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
