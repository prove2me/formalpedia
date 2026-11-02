-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_scalable_qft
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.scalable_qft
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:43:12.60201+00:00
-- url     : https://prove2.me/theorems/20c8e9c1-beb8-43fa-b4b7-9f4d8e127af1
-- title:
--   Exact scalable QFT assembly
-- statement:
--   Let $m,k\ge2$ be integers. Let $C_{m,k}$ be the chronological circuit obtained by starting with $QFT_m$ and, for each $t=1,\ldots,k-1$, applying adjacent two-block phase-swaps of types $t,t-1,\ldots,1$ at offsets $(t-1)m,(t-2)m,\ldots,0$, then $QFT_m$ at offset zero. A type-$j$ phase-swap maps $|a,b\rangle$ to $e^{2\pi iab/2^{(j+1)m}}|b,a\rangle$, with both integers read most significant bit first. The Fourier transform has positive exponential sign and normalization $2^{-km/2}$. Then
--
--   $$C_{m,k}=QFT_{km},\qquad \#QFT_m=k,\qquad\#CP=\binom{k}{2},\qquad\#CP_j=k-j\quad(1\le j<k).$$
--
--   There are no other phase-swap types. This is an exact assembly identity, including the complete final permutation and phase; it makes no physical timing claim.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 9, Abstract headline pinned to exact scalable QFT assembly, Fig. 7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF pp.1,9, abstract headline pinned to Fig.7: the exact scalable QFT
assembly and its actual block counts. No timing or global optimization claim. -/
theorem scalable_qft (m k : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ k) :
    blockCircuitMatrix (k * m) (qftAssembly m k) = qftQubits (k * m) ∧
    fourierCount (qftAssembly m k) = k ∧
    phaseTotal (qftAssembly m k) = Nat.choose k 2 ∧
    (∀ j, 1 ≤ j → j < k → phaseCount j (qftAssembly m k) = k - j) ∧
    (∀ j, j = 0 ∨ k ≤ j → phaseCount j (qftAssembly m k) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
