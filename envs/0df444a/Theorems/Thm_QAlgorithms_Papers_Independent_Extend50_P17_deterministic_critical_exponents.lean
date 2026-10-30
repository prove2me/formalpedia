-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_deterministic_critical_exponents
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.deterministic_critical_exponents
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:54:21.313996+00:00
-- url     : https://prove2.me/theorems/bdde2b68-2c70-4970-b495-2c92ef716cf3
-- title:
--   Table 2: deterministic packaged-PBT critical exponents
-- statement:
--   Consider integer schedules $N_t\to\infty$ and $1\le k_t\le N_t$ eventually, with $k_t\mid N_t$ and $k_t/N_t^\alpha\to a>0$, where $\alpha\le1$. All ports are qubits. Let $F_{\rm pack}$ be the product of $k_t$ single-port fixed-resource SRM fidelities and $F_{\rm pack}^{\rm OPBT}$ the product of optimal single-port fidelities. Their limits are
--
--   $$\lim F_{\rm pack}=\begin{cases}1&\alpha<1/2,\\e^{-3a^2/4}&\alpha=1/2,\\0&\alpha>1/2,\end{cases}\qquad\lim F_{\rm pack}^{\rm OPBT}=\begin{cases}1&\alpha<2/3,\\e^{-\pi^2a^3}&\alpha=2/3,\\0&\alpha>2/3.\end{cases}$$
--
--   For the fixed-resource MPBT SRM, $F_2(N_t,k_t)\to1$ if $\alpha<1$. If $\alpha=1$ and $a<1$, its limit exists and is at least $e^{-3a/(1-a)}$. Integer schedules preserve physical package sizes, including the zero-limit packaged case $\alpha=1$. No conclusion is inferred from the blank MPBT zero-limit cell.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 5, Table 2: deterministic packaged-PBT critical exponents

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.5, Table 2: both packaged exponents, plus both MPBT entries.
No MPBT converse is inferred from the empty table cell. -/
theorem deterministic_critical_exponents (N k : ℕ → ℕ) (a alpha : ℝ)
    (hsch : PackageSchedule N k) (ha : 0 < a)
    (hphysical : alpha ≤ 1) (hscale : Scales N k a alpha) :
    RegimeLimit N k packagedFidelity alpha (1/2) (Real.exp (-3*a^2/4)) ∧
    RegimeLimit N k packagedOptimalFidelity alpha (2/3) (Real.exp (-Real.pi^2*a^3)) ∧
    (alpha < 1 → Tendsto (fun t => mpbtFidelity 2 (N t) (k t)) atTop (nhds 1)) ∧
    (alpha = 1 → a < 1 → ∃ L : ℝ,
      Tendsto (fun t => mpbtFidelity 2 (N t) (k t)) atTop (nhds L) ∧
      Real.exp (-3*a/(1-a)) ≤ L) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
