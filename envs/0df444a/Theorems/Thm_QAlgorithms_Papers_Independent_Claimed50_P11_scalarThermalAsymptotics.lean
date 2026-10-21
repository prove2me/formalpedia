-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P11_scalarThermalAsymptotics
-- name    : QAlgorithms.Papers.Independent.Claimed50.P11.scalarThermalAsymptotics
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:23:00.351808+00:00
-- url     : https://prove2.me/theorems/ac0bf628-0ec2-42f7-95dc-b5fd5db36403
-- title:
--   Three scalar thermal-entropy asymptotics
-- statement:
--   Let $g(N)=(N+1)\ln(N+1)-N\ln N$ for $N\ge0$, with $0\ln0=0$, and let $g^{-1}$ be its inverse from $[0,\infty)$ to $[0,\infty)$. Write $e=\exp(1)$. As the respective real variables tend to $+\infty$,
--
--   $$
--   \begin{aligned}
--   g(x-\tfrac12)&=\ln(ex)+O(x^{-2}),\\
--   e^{g(N)}&=e(N+\tfrac12)+O(N^{-1}),\\
--   g^{-1}(\ln x)&=x/e-\tfrac12+O(x^{-1}).
--   \end{aligned}
--   $$
--
--   Each remainder is bounded in absolute value by a positive constant times the displayed reciprocal power beyond a fixed positive threshold. The constants and thresholds can differ between the three estimates. These scalar estimates compare entropy power and thermal occupation; they assert no uniform bound over quantum input states.
-- source:
--   A generalization of the Entropy Power Inequality to Bosonic Quantum Systems, arXiv:1402.0404v2, PDF p. 17, §IV.B Eq. (86); §VI.B Eqs. (103), (104)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P11

open Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Dependency50.P39 (attenuatorMatrix)

/-- PDF p.17 Eq.(86), PDF p.23 Eqs.(103),(104): all three scalar thermal
asymptotics, with independent constants before the corresponding variable.
The printed e multiplies x or N+1/2; it is not exp(x) or exp(N+1/2).
Positive thresholds keep every logarithm and reciprocal in its source domain. -/
theorem scalarThermalAsymptotics :
    (∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      |thermalEntropy (x - 1 / 2) - Real.log (Real.exp 1 * x)| ≤ C / x ^ 2) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      |Real.exp (thermalEntropy N) - Real.exp 1 * (N + 1 / 2)| ≤ C / N) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      |entropyPowerPhoton x - (x / Real.exp 1 - 1 / 2)| ≤ C / x) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P11

end
