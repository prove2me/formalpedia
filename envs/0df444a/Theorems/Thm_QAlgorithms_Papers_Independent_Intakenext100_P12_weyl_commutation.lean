-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_weyl_commutation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.weyl_commutation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:49:23.263034+00:00
-- url     : https://prove2.me/theorems/960b67bf-d40a-4832-89b5-b34005ee69d3
-- title:
--   §VI (44)–(46): Weyl commutation criterion
-- statement:
--   Let $N\ge1$ and write $v=(\alpha,\beta)$, $w=(\alpha',\beta')\in\mathbb R^{2N}$, in that grouped order. Define $U_v$ by its actual Schrödinger translation/modulation action, equivalently $U_v=e^{i\sqrt{2\pi}(\alpha\cdot p+\beta\cdot q)}$. Then
--
--   $$U_vU_w=e^{2\pi i\omega(v,w)}U_wU_v,\qquad\omega(v,w)=\alpha\cdot\beta'-\alpha'\cdot\beta.$$
--
--   The operators commute if and only if $\omega(v,w)\in\mathbb Z$. The statement uses the faithful translation/modulation representation, rather than arbitrary matrices assumed to satisfy a commutation rule.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 7, §VI (44)–(46): Weyl commutation criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section VI (44)–(46), PDF p.7: Weyl commutation and its exact integer criterion. -/
theorem weyl_commutation (N : ℕ) (hN : 0 < N) (v w : Phase N → ℝ) :
    (∀ psi x, schrodingerDisplacement N v (schrodingerDisplacement N w psi) x =
      cisPhase (2 * Real.pi * gkpPair N v w) * schrodingerDisplacement N w (schrodingerDisplacement N v psi) x) ∧
    ((∀ psi, schrodingerDisplacement N v (schrodingerDisplacement N w psi) = schrodingerDisplacement N w (schrodingerDisplacement N v psi)) ↔
      ∃ k : ℤ, gkpPair N v w = k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
