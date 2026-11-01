-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kification_preservesLimits
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kification_preservesLimits
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:26:34.511185+00:00
-- url     : https://prove2.me/theorems/fdbf07e4-7e71-4164-98f5-ffb20ab708cc
-- title:
--   Corollary B.7
-- statement:
--   Let $k:\mathrm{Top}\to\mathrm{kTop}$ be the functor assigning the final compact-Hausdorff-probe topology to each underlying set and the same function to each continuous map. Then
--
--   $$k\text{ preserves categorical limits}.$$
--
--   This is the categorical meaning of the source's word “continuous” for the coreflector, for arbitrary topological spaces without a separation axiom.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 36, Corollary B.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Corollary B.7, PDF p. 36: the specified coreflector preserves
categorical limits. No continuity of an unrelated function is substituted. -/
theorem kification_preservesLimits :
    Limits.PreservesLimits kCoreflector.{u} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
