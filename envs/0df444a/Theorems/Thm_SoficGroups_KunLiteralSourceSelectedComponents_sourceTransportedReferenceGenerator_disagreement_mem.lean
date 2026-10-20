-- Prove2me | Theorems.Thm_SoficGroups_KunLiteralSourceSelectedComponents_sourceTransportedReferenceGenerator_disagreement_mem
-- name    : SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerator_disagreement_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/2b547add-6a83-4efa-bb76-e8d59cc69cdc
-- title:
--   SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerator_disagreement_mem
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralSourceSelectedComponents

theorem SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerator_disagreement_mem
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (n : ℕ) (i : ↥SΓ) (x : Fin (A.model n).size)
    (h : sourceTransportedReferenceGenerators A SΓ n i x ≠
      ((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A).model n).action
        (SoficGroups.SourceProductThroughAlpha.sourceCompressionUAlphaEquiv
          (i : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode),
          1) x) :
    x ∈ sourceGeneratorFamilyConjugacyBad A SΓ n := by sorry
