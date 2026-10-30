-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_worst_average_optima
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.worst_average_optima
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:21:01.040997+00:00
-- url     : https://prove2.me/theorems/015db86b-8224-4653-a2be-8bab447e8b07
-- title:
--   Equality of worst and average weighted optima
-- statement:
--   Let $d,N\ge1$ and let $w_1,\ldots,w_N\in[0,1]$, without any sum normalization. For a CPTP joint channel $T:M_d\to M_d^{\otimes N}$, write $T_i$ for its ordinary partial-trace marginal and $F(\psi,T_i)=\langle\psi|T_i(|\psi\rangle\langle\psi|)|\psi\rangle$ for a unit vector $\psi$. With expectation under the normalized Haar pure-state law,
--
--   $$
--   \sup_{T\ \mathrm{CPTP}}\sum_{i=1}^N w_i\inf_{\|\psi\|=1}F(\psi,T_i)
--   =\sup_{T\ \mathrm{CPTP}}\sum_{i=1}^Nw_i\mathbb E_\psi F(\psi,T_i).
--   $$
--
--   Each marginal is minimized separately. The zero weight vector is included. The assertion compares the optimized objectives; it does not assert their equality for every unsymmetrized channel.
--
--   This permits average-fidelity optimization to solve the worst-fidelity problem.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 6, Theorem 4: worst and average weighted cloning optima agree

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.6, Theorem 4, objectives from pp.3–4: the two suprema over all channels agree.
Zero weights are allowed; each infimum is inside the sum. -/
theorem worst_average_optima (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    worstOptimum d N w = averageOptimum d N (by omega) w := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
