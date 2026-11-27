-- Prove2me | Theorems.Thm_RobustSAA_Discrete_Supplement_theorem_7
-- name    : RobustSAA.Discrete.Supplement.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T19:42:34.494243+00:00
-- url     : https://prove2.me/theorems/f937fd14-bdce-4c0f-b660-7d72a2d67b62
-- title:
--   Theorem 7 — on bounded support the LCX-based test is uniformly consistent
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be closed and bounded, and let the thresholds of the LCX-based test satisfy $Q_C(N)=Q_{C_N}(\alpha_1)\to0$ and $Q_R(N)=Q_{R_N}(\alpha_2)\to0$. Then the test with confidence regions (17) is uniformly consistent (Definition 3): for every law $F$ on $\Xi$ generating iid data, almost surely, every sequence of laws $F_N$ that does not converge weakly to $F$ satisfies
--
--   $$F_N\notin\mathcal F^{\alpha_1,\alpha_2}_{C_N,R_N}(\xi^1,\dots,\xi^N)\quad\text{for infinitely many }N.$$
--
--   By Theorem 2 of the paper, uniform consistency is what makes Robust SAA with this test converge in objective, optimal value and optimal solutions.
--
--   Differences from the source:
--   - reading: the LCX-based test → the test (17) for arbitrary threshold sequences Q_C(N) → 0 and Q_R(N) → 0; reason: §10.11 uses only these limits (p. 40)
--   - encoding: uniformly consistent (Definition 3) → the published RobustSAA.Convergence.IsUniformlyConsistent; reason: same definition, weak convergence in ProbabilityMeasure
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 7, p. 15 (proof §10.11, p. 40)

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_LCX

namespace RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Convergence

theorem theorem_7 {d : ℕ} (Ξ : Set (Pt d)) (hΞ : IsClosed Ξ) (hbdd : Bornology.IsBounded Ξ)
    (QC QR : ℕ → ℝ) (hQC : Tendsto QC atTop (𝓝 0)) (hQR : Tendsto QR atTop (𝓝 0)) :
    IsUniformlyConsistent (lcxDUS (Ξ := Ξ) QC QR) := by sorry

end RobustSAA.Discrete.Supplement
