-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_remark_4_4
-- name    : QAlgorithms.Papers.Independent.Information100.P50.remark_4_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:01:02.649405+00:00
-- url     : https://prove2.me/theorems/c96f9252-8b7e-4fba-b078-31fe8d0db9ac
-- title:
--   Remark 4.4: The constant one and exponent 1/2 in Proposition 4
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For scalar effects $E=\delta I_1$ and $E'=0$, $0\le\delta\le1$,
--
--   $$\|g_\#(E)-g_\#(E')\|_\infty=\sqrt{\delta(1-\delta)},\qquad \frac{\sqrt{\delta(1-\delta)}}{\sqrt\delta}\longrightarrow1\quad(\delta\downarrow0).$$
--
--   Here $g_\#(t)=\sqrt{t(1-t)}$. Every coefficient $0\le C<1$ fails somewhere in the exponent-$1/2$ bound; for every $\beta>1/2$ and every $C>0$, some $0<\delta<1$ satisfies $C\delta^\beta<\sqrt{\delta(1-\delta)}$. Thus both the constant and exponent in the operator inequality are sharp. No sharpness claim is made for a channel fidelity bound.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 14, Remark 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Remark 4.4, source PDF p.14: sharpness of the operator estimate, without asserting
sharpness of the channel fidelity bound. The denominator in the ratio is sqrt(delta). -/
theorem remark_4_4 :
    (∀ delta ∈ Icc (0 : ℝ) 1,
      specNorm (cfc gHash ((delta : ℂ) • (1 : M 1)) - cfc gHash (0 : M 1)) =
        Real.sqrt (delta * (1 - delta))) ∧
    Tendsto (fun delta : ℝ => Real.sqrt (delta * (1 - delta)) / Real.sqrt delta)
      (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    (∀ C : ℝ, 0 ≤ C → C < 1 → ∃ delta ∈ Ioo (0 : ℝ) 1,
      C * Real.sqrt delta < Real.sqrt (delta * (1 - delta))) ∧
    (∀ beta : ℝ, 1 / 2 < beta → ∀ C : ℝ, 0 < C → ∃ delta ∈ Ioo (0 : ℝ) 1,
      C * Real.rpow delta beta < Real.sqrt (delta * (1 - delta))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
