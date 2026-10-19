-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_positiveL1MuCompact
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.positiveL1MuCompact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:13:07.517603+00:00
-- url     : https://prove2.me/theorems/28f0610e-eea3-4cf0-b586-50fd193f3c0c
-- title:
--   Proposition 9: positive ℓ¹ unit part
-- statement:
--   In the real Banach space $\ell^1(\mathbb N)$ with its norm topology, the positive closed unit part
--   $$A_1=\{x:x_i\ge0\text{ for all }i,\ \|x\|_1\le1\}$$
--   is $\mu$-compact, using Borel probabilities and the Pettis barycenter.
--
--   The bounded-part convention is the intersection with the closed unit ball.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 10, Proposition 9: positive ℓ¹ unit part

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section LpResults

/-- Proposition 9, PDF p.10 and footnote 3: the positive l^1 closed unit
part, rather than the entire unbounded positive cone, is µ-compact. -/
theorem positiveL1MuCompact : MuCompact (positiveLpUnitPart 1) := by sorry

end LpResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
