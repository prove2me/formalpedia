-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P72_highModulationThreshold
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P72.highModulationThreshold
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T07:44:26.082604+00:00
-- url     : https://prove2.me/theorems/59d1c255-d7fe-4a03-9993-e2c6e9586b67
-- title:
--   High-modulation added-noise threshold and squeezing monotonicity
-- statement:
--   Let $G>0$, $|1-G|\le G\chi$, and fix $s>0$. For finite real modulation $V$, put $P_V=(G\chi+Gs)(G\chi+G/V)$ and $T_G(s)=(\sqrt{G^2s^2+4}-Gs)/2$. Then
--
--   $$
--   \lim_{V\to\infty}P_V=G\chi(G\chi+Gs),\qquad
--   G\chi(G\chi+Gs)<1\iff (G\chi)^2+Gs(G\chi)-1<0\iff G\chi<T_G(s).
--   $$
--
--   For $0<s_1\le s_2$, $T_G(s_2)\le T_G(s_1)$. Thus stronger squeezing (smaller residual preparation variance) permits a larger added output-noise expression. At fixed positive $s$, the preparation interval $1/V\le s\le V$ holds for sufficiently large $V$.
--
--   The limit concerns finite-modulation expressions and does not posit an infinite-temperature density operator or turn a boundary equality into positive information advantage.
-- source:
--   Reverse reconciliation protocols for quantum cryptography with continuous variables, arXiv:quant-ph/0204127v1, PDF p. 4, III.C, (49)–(52): high-modulation noise threshold and squeezing monotonicity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

noncomputable section

open Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P72

/-- Grosshans--Grangier, PDF p.4, III.C, (49)--(52).
V tends to infinity through finite real values, at fixed positive s.
The strict limiting criterion is not equated to a non-strict finite-V bound. -/
theorem highModulationThreshold
    (G chi s : ℝ) (hG : 0 < G) (hchi : |1 - G| ≤ G * chi) (hs : 0 < s) :
    Tendsto (fun V : ℝ => varianceProduct G chi V s) atTop
      (nhds (G * chi * (G * chi + G * s))) ∧
    ((G * chi * (G * chi + G * s) < 1) ↔
      ((G * chi) ^ 2 + G * s * (G * chi) - 1 < 0)) ∧
    ((G * chi * (G * chi + G * s) < 1) ↔ G * chi < noiseThreshold G s) ∧
    (∀ s1 s2 : ℝ, 0 < s1 → s1 ≤ s2 →
      noiseThreshold G s2 ≤ noiseThreshold G s1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P72

end
