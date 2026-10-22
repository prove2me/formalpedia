-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_entropy_continuity
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.entropy_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:13:05.273653+00:00
-- url     : https://prove2.me/theorems/52cab573-8c37-4ffe-aff0-d3dd129d55fd
-- title:
--   Entropy continuity in squared fidelity
-- statement:
--   Let $\rho$ and $\sigma$ be density operators on a complex Hilbert space of positive finite dimension $d$. Let $F(\rho,\sigma)$ be squared Uhlmann fidelity and let $S$ denote von Neumann entropy in bits. If $2\sqrt{1-F(\rho,\sigma)}<1/3$, then
--
--   $$|S(\rho)-S(\sigma)|\leq2\sqrt{1-F(\rho,\sigma)}\log_2d+1.$$
--
--   This is the source's quantitative entropy-continuity estimate on its strict fidelity domain.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 5, Lemma 6, Eqs.(37)–(38)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.5, Lemma 6, Eqs.(37)--(38): squared fidelity and the strict domain
2 sqrt(1-F)<1/3, with entropy in bits. -/
theorem entropy_continuity {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hclose : 2 * Real.sqrt (1 - squaredFidelity rho sigma) < (1 : ℝ) / 3) :
    |vnEntropy rho - vnEntropy sigma| ≤
      2 * Real.sqrt (1 - squaredFidelity rho sigma) * Real.logb 2 (Fintype.card I : ℝ) + 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
