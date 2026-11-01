-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kOmega_quotient
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kOmega_quotient
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:29:39.545261+00:00
-- url     : https://prove2.me/theorems/885305cd-bca6-4a4e-aef0-c4a46f74ad03
-- title:
--   Lemma C.3
-- statement:
--   Let $X$ and $Y$ be topological spaces and $q:X\to Y$ a surjective quotient map. If $X$ is k-omega in the compact-Hausdorff final-topology sense of Definition C.1, then
--
--   $$Y\text{ is k-omega}.$$
--
--   No Hausdorffness assumption is added to the quotient. Thus the conclusion uses the same class of spaces as the source's definition.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 38, Lemma C.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Lemma C.3, PDF p. 38: every quotient of a k-omega space is k-omega. -/
theorem kOmega_quotient
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IsKOmega X) (q : X → Y) (hq : IsQuotientMap q) :
    IsKOmega Y := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
