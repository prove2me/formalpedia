-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_scalable_qft_variantII
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.scalable_qft_variantII
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:48:31.337854+00:00
-- url     : https://prove2.me/theorems/d5daac2a-5d16-486d-9d19-c1f4ba9fb16a
-- title:
--   Exact QFT assembly with half-block phase-swaps
-- statement:
--   Let $m\ge2$ be even and let $k\ge2$. In the Fig. 7 circuit replace each phase-swap of type $j$ and half-width $m=2h$, at offset $a$, by the chronological four-module list
--
--   $$CP_{2j}(a+h),\quad CP_{2j-1}(a),\quad CP_{2j+1}(a+2h),\quad CP_{2j}(a+h),$$
--
--   where each new module has half-width $h$ and total width $m$. The resulting explicit Fig. 16 circuit satisfies
--
--   $$C^{\rm II}_{m,k}=QFT_{km},\qquad\#QFT_m=k,\qquad\#CP=4\binom{k}{2}.$$
--
--   Only phase indices $1,\ldots,2k-1$ occur. This preserves every phase and permutation. Three bottom label occurrences printed $2m$ (two phase types) in Fig. 16 are interpreted as $m$, following the caption and half-block construction; this minimal arity correction was independently checked in moderation round 1.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 19, Appendix A, Fig. 16: QFT variant II

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF p.19, Fig.16: exact QFT variant II. The three printed bottom arity
labels 2m (two phase types) are read as m, as required by the caption and half-block widths;
this correction is recorded for independent moderation. -/
theorem scalable_qft_variantII (m k : ℕ) (hm : 2 ≤ m) (heven : Even m) (hk : 2 ≤ k) :
    blockCircuitMatrix (k * m) (qftAssemblyII m k) = qftQubits (k * m) ∧
    fourierCount (qftAssemblyII m k) = k ∧
    phaseTotal (qftAssemblyII m k) = 4 * Nat.choose k 2 ∧
    (∀ j, j = 0 ∨ 2 * k ≤ j → phaseCount j (qftAssemblyII m k) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
