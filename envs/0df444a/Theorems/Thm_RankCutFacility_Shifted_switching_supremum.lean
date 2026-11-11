-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_switching_supremum
-- name    : RankCutFacility.Shifted.switching_supremum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:28.139523+00:00
-- url     : https://prove2.me/theorems/f7164262-cc18-48ae-b41a-54b1db50e270
-- title:
--   Section 4.6, equation (29) — All switching indices equal the limiting supremum
-- statement:
--   For real parameters $1/8\le\mu\le1$ and $0<\delta\le1/2$, use exactly the sequence in (23), with every positive integer $h$. The set of sequence values is nonempty and bounded above as part of the conclusion.
--
--   In fact, for 1/8 ≤ µ ≤ 1 and 0 < δ ≤ 1/2,
--   $$
--   \sup_{h\ge1}\Gamma_h(\mu,\delta)=\frac{e^{-(1+\mu)}}\mu.\tag{29}
--   $$
--
--   This controls every switching index rather than a finite numerical truncation.
--
--   Differences from the source:
--   - encoding: the real supremum in (23) or (29) → sSup together with explicit nonemptiness and boundedness conclusions; reason: this excludes the default value of an unbounded real supremum without adding a hypothesis
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Section 4.6, equation (29), printed p. 15 (PDF p. 17), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem switching_supremum (μ δ : ℝ) (hμ : (1:ℝ)/8 ≤ μ ∧ μ ≤ 1)
    (hδ : 0 < δ ∧ δ ≤ (1:ℝ)/2) :
    (gammaSet μ δ).Nonempty ∧ BddAbove (gammaSet μ δ) ∧
      sSup (gammaSet μ δ) = Real.exp (-(1+μ))/μ := by sorry
end RankCutFacility.Shifted
