-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_truncated_cpSwap_panels
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.truncated_cpSwap_panels
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:49:08.378273+00:00
-- url     : https://prove2.me/theorems/e398d88c-57c1-40c7-8928-38a30fe04259
-- title:
--   Exact truncated phase-swap circuit equivalences
-- statement:
--   On two five-bit blocks, a type-$j\ge1$ phase-swap exchanges the blocks and contributes one pair phase $\pi/2^{5(j-1)+1+a+b}$ for each occupied bit pair $a,b\in\{0,\ldots,4\}$. Delete angles strictly below $\pi/1024$, retaining equality. Let $\widetilde{CP}_j$ denote this truncated module. Define panels A, B, C by moving each second-block bit left across the five first-block bits with adjacent phase-SWAP crossings, in the order drawn in Fig. 17. Then
--
--   $$\widetilde{CP}_1=CP_1=C_A,\qquad\widetilde{CP}_2=C_B,\qquad\widetilde{CP}_j=SWAP_{5,5}=C_C\quad(j\ge3).$$
--
--   Panel A retains all 25 pair phases, from $\pi/2$ to $\pi/512$. Panel B retains exactly $a+b\le4$, with angles $\pi/64$ through $\pi/1024$. Panel C is the pure block exchange. These are exact equalities of truncated modules and do not assert the undefined whole-QFT relative-error claim.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 19, Appendix B, Fig. 17: truncated cp-swap circuit equivalences

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF pp.10,19, Appendix B Fig.17: exact equivalence of all three
truncated circuits. This makes no whole-QFT approximation-error claim. -/
theorem truncated_cpSwap_panels :
    (truncatedCpSwap 5 1 10 = cpSwap 5 1 ∧
      truncatedCpSwap 5 1 10 = blockCircuitMatrix 10 panelA) ∧
    truncatedCpSwap 5 2 10 = blockCircuitMatrix 10 panelB ∧
    (∀ j : ℕ, 3 ≤ j → truncatedCpSwap 5 j 10 = blockSwap 5 ∧
      truncatedCpSwap 5 j 10 = blockCircuitMatrix 10 panelC) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
