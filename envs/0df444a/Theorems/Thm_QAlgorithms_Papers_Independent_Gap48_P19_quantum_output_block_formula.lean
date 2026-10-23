-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P19_quantum_output_block_formula
-- name    : QAlgorithms.Papers.Independent.Gap48.P19.quantum_output_block_formula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:12:24.916428+00:00
-- url     : https://prove2.me/theorems/348dd8e3-9360-4d62-8cf1-018b6411cb83
-- title:
--   The selected density output equals the indexed block formula
-- statement:
--   Let $\rho_{AB},\sigma_{A'B'}$ be independent density matrices on finite nonzero local spaces, with $A'=A=a=a'$ and $B'=B=b=b'$ up to basis labels. Let $U$ be unitary on $AA'$ and, for each measured value $a$, let $V_a$ be unitary on $BB'$. Write $R$ for $\rho\otimes\sigma$ regrouped as $AA':BB'$, $W_a=U\otimes V_a$, $\Pi_a=|a\rangle\langle a|\otimes I$, and let $C=\langle a_0,b_0|\sum_a\Pi_a W_a R W_a^*\Pi_a|a_0,b_0\rangle$. Set $p=\operatorname{Tr}C$ and assume $p>0$. Then $\omega=C/p$ is a density matrix, its off-diagonal Alice blocks vanish, and
--
--   $$\omega_{(a,b_1),(a,b_2)}=\frac1p\sum_{i,j}U_{(a,a_0),i_A}(V_a)_{(b_1,b_0),i_B}\rho_{(i_{A1},i_{B1}),(j_{A1},j_{B1})}\sigma_{(i_{A2},i_{B2}),(j_{A2},j_{B2})}\overline{(V_a)_{(b_2,b_0),j_B}}\,\overline{U_{(a,a_0),j_A}}.$$
--
--   Here $i_A,j_A$ index $AA'$ and $i_B,j_B$ index $BB'$, so the sum has eight scalar indices. This is the density construction and block equivalence of (25)-(31).
-- source:
--   Entanglement of Distillation and Conditional Mutual Information, arXiv:quant-ph/0202144v2, PDF p. 7, §4, Eqs.(25)-(31)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6-7, (22)-(31): at positive success, (25) is a density matrix,
with block entries (26)-(31) and no off-diagonal Alice blocks. -/
theorem quantum_output_block_formula {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho sigma : Mat (A × B)) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (U : Matrix.unitaryGroup (A × A) ℂ) (V : A → Matrix.unitaryGroup (B × B) ℂ)
    (a0 : A) (b0 : B) (hsuccess : 0 < quantumSuccess rho sigma U V a0 b0) :
    IsDensityMatrix (measuredSelectionOutput rho sigma U V a0 b0) ∧
    (∀ a b1 b2, measuredSelectionOutput rho sigma U V a0 b0 (a, b1) (a, b2) =
      quantumBlock rho sigma U V a0 b0 a b1 b2) ∧
    (∀ a1 a2 b1 b2, a1 ≠ a2 →
      measuredSelectionOutput rho sigma U V a0 b0 (a1, b1) (a2, b2) = 0) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P19
