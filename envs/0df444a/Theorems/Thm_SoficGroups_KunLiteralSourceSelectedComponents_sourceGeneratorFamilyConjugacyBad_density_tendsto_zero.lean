-- Prove2me | Theorems.Thm_SoficGroups_KunLiteralSourceSelectedComponents_sourceGeneratorFamilyConjugacyBad_density_tendsto_zero
-- name    : SoficGroups.KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/62ebc1e8-6e8f-44c3-bba2-91ab383e5c78
-- title:
--   SoficGroups.KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad_density_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralSourceSelectedComponents
open Filter Topology
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.SourceProductThroughAlpha
open scoped BigOperators Pointwise

theorem SoficGroups.KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad_density_tendsto_zero
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) :
    Tendsto
      (fun n =>
        ((sourceGeneratorFamilyConjugacyBad A S n).card : ℝ) /
          (A.model n).size)
      atTop (nhds 0) := by sorry
