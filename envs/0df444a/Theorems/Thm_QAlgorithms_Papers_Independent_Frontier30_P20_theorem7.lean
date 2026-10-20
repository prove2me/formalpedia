-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem7
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:37:38.406366+00:00
-- url     : https://prove2.me/theorems/f514afec-ff2d-4539-af81-29ddfb093686
-- title:
--   Theorem 7 (Bounds on the determinant)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. For a channel $T$, let $\tau=(T\otimes\mathrm{id})(|\Omega\rangle\langle\Omega|)$ with $|\Omega\rangle=d^{-1/2}\sum_i|ii\rangle$. Then
--
--   $$\det T\le(\operatorname{tr}\tau^2)^{d^2/2}.$$
--
--   For each fixed $d$ there are constants $C,\eta>0$ such that every channel with $\det T>1-\eta$ and every unitary conjugation $U_0$ maximizing $\operatorname{tr}_{\mathcal H}(TU)$ satisfy
--
--   $$\|T-U_0^{-1}\|\le C\sqrt{1-\det T}.$$
--
--   The constants are uniform over $T$ and all maximizers. The inverse is an actual two-sided inverse. This quantifies proximity to a unitary as the determinant approaches one.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 9, Theorem 7 (Bounds on the determinant)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 7, PDF pp.9--10: normalized Choi purity and uniform local square-root bound.
The constants may depend on d, but precede T and every maximizing unitary. -/
theorem theorem7 {d : ℕ} (hd : 0 < d) :
    (∀ T : Super d, Channel T → determinant T ≤
      Real.rpow (((jamiolkowskiState T) * jamiolkowskiState T).trace.re) ((d : ℝ) ^ 2 / 2)) ∧
    (∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ ∀ T U : Super d,
      Channel T → Maximizer T U → 1 - eta < determinant T →
      ∀ V : Super d, V * U = 1 → U * V = 1 →
        hsOperatorNorm (T - V) ≤ C * Real.sqrt (1 - determinant T)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
