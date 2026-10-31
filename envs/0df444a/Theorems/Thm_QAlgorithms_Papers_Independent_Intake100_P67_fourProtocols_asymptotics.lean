-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_fourProtocols_asymptotics
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.fourProtocols_asymptotics
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:28:09.47866+00:00
-- url     : https://prove2.me/theorems/6ccf581b-bc4a-4cb3-b4a5-f2d9dc6b4dd4
-- title:
--   Asymptotic perfection and leading defects of all four protocols
-- statement:
--   Let $F_{\rm ME}(N)$ and $f_{\rm ME}(N)=(2F_{\rm ME}(N)+1)/3$ be the fixed-resource SRM entanglement and Haar average fidelities from (29). Let $f_{\rm opt}(N)$ be (42), $p_{\rm ME}(N)$ the faithful fixed-resource success (50), and $p_{\rm opt}(N)=N/(N+3)$. As positive integers $N$ tend to infinity, all five quantities tend to one. Their leading defects satisfy
--
--   $$N(1-F_{\rm ME})\to\frac34,\quad N(1-f_{\rm ME})\to\frac12,\quad N^2(1-f_{\rm opt})\to\frac{2\pi^2}{3},$$
--
--   $$\sqrt N(1-p_{\rm ME})\to\sqrt{\frac8\pi},\qquad N(1-p_{\rm opt})\to3.$$
--
--   The probabilistic protocols are exactly faithful on success, so their vanishing defect is failure probability. The limits retain the leading asymptotics rather than replacing them by convergence alone.
--
--   They distinguish the fixed and optimized resources in both versions.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 10, §§IV A–B, VI A–B, IX; Eqs. (30),(42),(51),(56)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.5,7–8,10, Eqs.(30),(42),(51),(56): all four protocols tend to perfection,
with leading defects, not merely convergence. The root in Eq.(51) covers 8/(pi*N). -/
theorem fourProtocols_asymptotics :
    Filter.Tendsto fixedFidelity Filter.atTop (nhds 1) ∧
    Filter.Tendsto (fun N => (2 * fixedFidelity N + 1) / 3) Filter.atTop (nhds 1) ∧
    Filter.Tendsto deterministicOptimumAverage Filter.atTop (nhds 1) ∧
    Filter.Tendsto fixedSuccess Filter.atTop (nhds 1) ∧
    Filter.Tendsto probabilisticOptimumSuccess Filter.atTop (nhds 1) ∧
    Filter.Tendsto (fun N : ℕ => (N : ℝ) * (1 - fixedFidelity N))
      Filter.atTop (nhds (3 / 4)) ∧
    Filter.Tendsto (fun N : ℕ => (N : ℝ) * (1 - (2 * fixedFidelity N + 1) / 3))
      Filter.atTop (nhds (1 / 2)) ∧
    Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (1 - deterministicOptimumAverage N))
      Filter.atTop (nhds (2 * Real.pi ^ 2 / 3)) ∧
    Filter.Tendsto (fun N : ℕ => Real.sqrt N * (1 - fixedSuccess N))
      Filter.atTop (nhds (Real.sqrt (8 / Real.pi))) ∧
    Filter.Tendsto (fun N : ℕ => (N : ℝ) * (1 - probabilisticOptimumSuccess N))
      Filter.atTop (nhds 3) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
