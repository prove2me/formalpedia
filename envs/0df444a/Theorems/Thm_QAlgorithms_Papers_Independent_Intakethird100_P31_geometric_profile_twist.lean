-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P31_geometric_profile_twist
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P31.geometric_profile_twist
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:41:59.942129+00:00
-- url     : https://prove2.me/theorems/0643c658-4c23-4ef0-a4a0-193e57b0740d
-- title:
--   Twist dependence of the explicit leading geometric coefficient
-- statement:
--   Let $N\ge1$ be an integer, and let $G_T$ denote the independently constructed zero-mean square-torus Green function. Consider the explicit coefficient profile on the right-hand side of (5.31),
--
--   $$g_N(\phi)=\frac{\pi N}{3(N+8)}G_T(\phi,\phi).$$
--
--   For every such $N$, its antiperiodic value is
--
--   $$g_N(\pi)=-\frac{N\log2}{12(N+8)}<0.$$
--
--   For even $N$, so that arbitrary twists are allowed, $g_N$ is nonincreasing on $0<\phi<\pi$, and
--
--   $$\lim_{\phi\downarrow0}\frac{g_N(\phi)}{\log\phi}=-\frac{N}{6(N+8)}.$$
--
--   In particular, this coefficient is positive for all sufficiently small positive twists. These statements analyze the explicit epsilon coefficient first; they do not assert a joint small-twist/epsilon expansion or a value of the physical entropy at zero twist.
--
--   This describes the sign and twist dependence of the analytic profile; the derivation identifying it with the Wilson–Fisher entropy coefficient is the separately inventoried node (5.31).
-- source:
--   Entanglement Entropy in the O(N) model, arXiv:0904.4477v1, PDF p. 30, §V C (5.32)–(5.33): twist dependence of the leading geometric coefficient

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P31

noncomputable section

open Filter Set MeasureTheory

open scoped Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P31

/-- PDF pp.30--31, Fig.10 and (5.32)--(5.33): twist dependence of the
explicit leading coefficient profile, after epsilon-coefficient extraction.
Arbitrary twists use even N. The antiperiodic value is available for every
positive N. No assertion is made about the physical zero-twist entropy. -/
theorem geometric_profile_twist (N : ℕ) (hN : 0 < N) :
    geometricProfile N Real.pi =
      -(N : ℝ) * Real.log 2 / (12 * ((N : ℝ) + 8)) ∧
    geometricProfile N Real.pi < 0 ∧
    (Even N →
      AntitoneOn (geometricProfile N) (Ioo (0 : ℝ) Real.pi) ∧
      Tendsto (fun phi : ℝ => geometricProfile N phi / Real.log phi)
        (𝓝[>] (0 : ℝ)) (𝓝 (-(N : ℝ) / (6 * ((N : ℝ) + 8)))) ∧
      (∀ᶠ phi : ℝ in 𝓝[>] (0 : ℝ), 0 < geometricProfile N phi)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P31

end
