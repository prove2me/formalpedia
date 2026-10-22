-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P42_private_bit_rate
-- name    : QAlgorithms.Papers.Independent.Gap48.P42.private_bit_rate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:36:06.46299+00:00
-- url     : https://prove2.me/theorems/3b8c9007-9f9a-4b0d-8f1e-973d13463174
-- title:
--   Corrected quantitative private-bit filtering and distillation bound
-- statement:
--   Consider the preceding private-state construction with exactly two parties, $d=2$, arbitrary positive finite local shields, normalized shield state $\rho$ and joint-shield unitaries $U_0,U_1$. For normalized local product vectors $f=f_1\otimes f_2$ and $g=g_1\otimes g_2$, define
--
--   $$
--   \eta=\max_{f,g}|\langle f|U_0\rho U_1^\dagger|g\rangle|.
--   $$
--
--   The maximum is attained. For every maximizing pair, put $a=\langle f|U_0\rho U_0^\dagger|f\rangle$ and $b=\langle g|U_1\rho U_1^\dagger|g\rangle$. Then $a,b,\eta>0$ and $\eta\le\sqrt{ab}$. The balanced local success filters are contractions. Their joint unnormalized output equals $q[p\Phi_++(1-p)\Phi_-]$, with trace $q$, where $\Phi_\pm$ are the projectors onto $(|00\rangle\pm|11\rangle)/\sqrt2$, and
--
--   $$
--   q=\min(a,b),\qquad p=\frac12+\frac{\eta}{2\sqrt{ab}},\qquad
--   E_D(\gamma^{(2)})\ge q[1-H_2(p)]>0.
--   $$
--
--   Here $0<q\le1$, $1/2<p\le1$, and $H_2(p)=-p\log_2p-(1-p)\log_2(1-p)$ with zero terms defined by continuity. The balanced filters use the same maximizing vectors and remove the phase of their cross matrix element. The yield is per original input copy, so it includes the success probability. This makes the strict positivity quantitative.
--
--   **Source correction.** Eq. (2.4) prints $\max(a,b)$; its two filtering cases instead give $\min(a,b)$.
-- source:
--   Quantum states representing perfectly secure bits are always distillable, arXiv:quant-ph/0602176v2, PDF p. 2, II.A, Eqs. (2.2)–(2.4); note [11]

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

namespace QAlgorithms.Papers.Independent.Gap48.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, Eqs.(2.2)--(2.4), note [11] p.5. Source correction:
printed a_max=max(a_1,a_2) is changed to min(a_1,a_2), since the two
filtering cases succeed with the smaller weight. The Bell parameter remains
1/2+eta/(2 sqrt(a_1*a_2)). Maximizers exist and no a_s is an input parameter. -/
theorem private_bit_rate (S : Fin 2 → ℕ) (hS : ∀ k, 0 < S k)
    (rho : Matrix (PartyBasis S) (PartyBasis S) ℂ) (hrho : IsDensityMatrix rho)
    (U : Fin 2 → Matrix.unitaryGroup (PartyBasis S) ℂ) :
    (∃ f g : ProductVectors S, Maximizes (shieldBlock rho U 0 1) f g) ∧
    ∀ f g : ProductVectors S, Maximizes (shieldBlock rho U 0 1) f g →
      PairConclusion rho U 0 1 f g := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P42
