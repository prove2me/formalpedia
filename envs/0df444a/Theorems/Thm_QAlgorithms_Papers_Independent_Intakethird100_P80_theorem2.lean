-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_theorem2
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.theorem2
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:23:55.150206+00:00
-- url     : https://prove2.me/theorems/96f2ae87-e5b5-4a12-ace8-afcf53187a51
-- title:
--   Finite attained correlated minimax value and saddle point
-- statement:
--   For a fixed finite quantum experiment $Q$, use the full setting simplex $\Sigma$ and the full local-theory simplex $\Pi$. Put $U(\sigma,\pi)=D_2(Q_\sigma\|P_{\sigma;\pi})$. There are $0\le V<\infty$, $\sigma^*\in\Sigma$, and $\pi^*\in\Pi$ such that
--
--   $$\inf_{\pi\in\Pi}\sup_{\sigma\in\Sigma}U(\sigma,\pi)=V=\sup_{\sigma\in\Sigma}\inf_{\pi\in\Pi}U(\sigma,\pi),$$
--
--   both outer extrema are attained at the displayed strategies, and for every $\sigma\in\Sigma$ and $\pi\in\Pi$,
--
--   $$U(\sigma,\pi^*)\le U(\sigma^*,\pi^*)=V\le U(\sigma^*,\pi).$$
--
--   This supplies an actual saddle point for potentially correlated settings. The minimizer inequality agrees with both the display in Definition 4 on PDF p.13 and the proof on p.35; the supplied plan incorrectly described the displayed inequality as reversed.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 14, Theorem 2: finite attained correlated minimax value

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

/-- PDF p.14, Theorem 2; proof p.35: finite correlated value, both attainments,
and both saddle inequalities (matching the source display on p.13). -/
theorem theorem2 {S : BellExperiment} (Q : Table S) (hQ : NonlocalityProof Q) :
    ∃ V : ℝ≥0∞, 0 ≤ V ∧ V < ⊤ ∧
      minimax Q (stdSimplex ℝ (Settings S)) = V ∧ correlatedStrength Q = V ∧
      ∃ (s : Sigma S) (p : PiLocal S),
        upperValue Q (stdSimplex ℝ (Settings S)) p.1 = V ∧ lowerValue Q s.1 = V ∧
        statisticalPayoff Q s.1 p.1 = V ∧ Saddle Q (stdSimplex ℝ (Settings S)) s.1 p.1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
