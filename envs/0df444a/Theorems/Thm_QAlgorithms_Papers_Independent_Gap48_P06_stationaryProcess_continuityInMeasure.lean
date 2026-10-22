-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P06_stationaryProcess_continuityInMeasure
-- name    : QAlgorithms.Papers.Independent.Gap48.P06.stationaryProcess_continuityInMeasure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:08:18.989832+00:00
-- url     : https://prove2.me/theorems/47f71f38-3c21-492d-91b3-2712cd764f16
-- title:
--   Strong continuity gives stochastic continuity
-- statement:
--   Let $G$ be a topological group, and let $\nu$ be the stationary probability distribution of a real-valued process on the canonical path space $\mathbb R^G$, with its coordinate-generated sigma-algebra. Write $X_g(\omega)=\omega(g)$ and assume $X_1\in L^2(\nu)$. If the shift representation on complex $L^2(\nu)$ is strongly continuous, then
--
--   $$\lim_{g\to1}\nu\{|X_g-X_1|\ge\varepsilon\}=0\qquad(\varepsilon>0).$$
--
--   Stationarity makes every coordinate square-integrable. The representation is the actual pullback of the canonical path shifts, so the conclusion concerns the given process law. This is the necessary continuity condition for a stationary process.
-- source:
--   Reflection Positive Stochastic Processes Indexed by Lie Groups, arXiv:1510.07445v3, PDF p. 44, Corollary A.2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P06

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped Topology ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P06

/-- Corollary A.2, PDF p.44: on the canonical distribution space of a
square-integrable stationary real process, strong continuity gives continuity
in measure of X_g at the identity. The single L2 hypothesis at 1 suffices by
stationarity, and all events use the same probability law. -/
theorem stationaryProcess_continuityInMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (nu : Measure (G → ℝ)) [IsProbabilityMeasure nu]
    (hstationary : ∀ g, MeasurePreserving (pathShift g) nu nu)
    (hsquare : MemLp (fun w : G → ℝ => w 1) 2 nu)
    (hstrong : ∀ f, Continuous (fun g => pathKoopman nu hstationary g f)) :
    ∀ eps : ℝ, 0 < eps →
      Tendsto (fun g => nu {w | eps ≤ |w g - w 1|}) (𝓝 (1 : G)) (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P06

end
