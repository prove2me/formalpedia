-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_purifiedFidelityConvex
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.purifiedFidelityConvex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:37:14.760068+00:00
-- url     : https://prove2.me/theorems/eb28bef2-b522-4a15-82b6-2b4d68596d25
-- title:
--   Appendix A2, Eq.(A3): convexity of purified channel-pair fidelity
-- statement:
--   Fix CPTP maps $\mathcal E,\mathcal F$ on a positive finite register. Let $G_F(\rho)$ be the squared fidelity of their extended outputs on the canonical square-root purification of $\rho$. For any finite probability vector $p_j\ge0$, $\sum_jp_j=1$, and normalized density matrices $\rho_j$,
--
--   $$G_F\left(\sum_jp_j\rho_j\right)\le\sum_jp_jG_F(\rho_j).$$
--
--   This is convexity of the purified channel-pair objective, rather than concavity of squared state fidelity. The block-diagonal expression in the source proof is $(\sum_jp_j\sqrt{G_F(\rho_j)})^2\le\sum_jp_jG_F(\rho_j)$; (A3) is retained unchanged.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 13, Appendix A2, Eq.(A3): convexity of purified channel-pair fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Appendix A2, PDF p.13, Eq.(A3): convexity of the actual purified SQUARED fidelity.
The block-diagonal root-fidelity algebra in the proof yields an inequality, not the printed
implicit equality with the weighted squared fidelities; Eq.(A3) itself is unchanged. -/
theorem purifiedFidelityConvex (E F : FiniteProcess I I) {L : Type} [Fintype L]
    (p : L → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (rho : L → ProcessDensityInput I) :
    purifiedFidelity E.val F.val (∑ j, (p j : ℂ) • (rho j).val) ≤
      ∑ j, p j * purifiedFidelity E.val F.val (rho j).val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
