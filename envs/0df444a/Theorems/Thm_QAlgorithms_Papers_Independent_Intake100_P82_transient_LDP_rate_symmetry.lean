-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_transient_LDP_rate_symmetry
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.transient_LDP_rate_symmetry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:10:16.225379+00:00
-- url     : https://prove2.me/theorems/7e8c75d3-2d3a-4d9e-ac90-a3f4f66ed39d
-- title:
--   Proposition 1.4: transient FR plus FT gives rate symmetry
-- statement:
--   For each positive integer $n$, let $(\Omega_n,\mathcal F_n,P_n)$ be an arbitrary probability space and let $\Theta_n$ be a measurable involution. Assume $\widehat P_n=(\Theta_n)_*P_n$ and $P_n$ are mutually absolutely continuous. Write $\sigma_n=\log(dP_n/d\widehat P_n)$ for a real almost-everywhere representative. No finite moment assumption is imposed.
--
--   Suppose $\sigma_n/n$ satisfies the full speed-$n$ LDP with a lower semicontinuous nonnegative extended rate $I$. Then
--   $$I(-s)=I(s)+s\qquad(s\in\mathbb R).$$
--   Convexity and compact sublevels are not assumptions. This derives the asymptotic rate symmetry from the transient reversal structure.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 13, Proposition 1.4: transient FR plus FT gives rate symmetry

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

noncomputable section

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

/-- Proposition 1.4, arXiv:1712.05167v3, PDF p.13. General varying sample
spaces; the rate is lower semicontinuous and nonnegative through FullLDP,
without assuming convexity or goodness. -/
theorem transient_LDP_rate_symmetry (O : ℕ → Type*) [∀ n, MeasurableSpace (O n)]
    (D : (n : ℕ) → ReversalExperiment (O n)) (I : ℝ → EReal)
    (hft : FullLDP (fun n A => (D n).law {x | experimentLogDensity (D n) x / (n : ℝ) ∈ A}) I) :
    ∀ s : ℝ, I (-s) = I s + (s : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P82

end
