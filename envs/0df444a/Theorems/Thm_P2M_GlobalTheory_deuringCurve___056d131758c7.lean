-- Prove2me | Theorems.Thm_P2M_GlobalTheory_deuringCurve___056d131758c7
-- name    : P2M_GlobalTheory_deuringCurve___056d131758c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:43.854082+00:00
-- url     : https://prove2.me/theorems/7296f703-49d3-44ae-9235-cc17bdef0837
-- title:
--   P2 M Global Theory deuring Curve   056d131758c7: P2 M Global Theory deuring Curve   056d131758c7
-- statement:
--   The P2 M Global Theory deuring Curve   056d131758c7 construction uses the P2 M Global Theory deuring Curve   056d131758c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L82-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {R : Type*} [CommRing R]

theorem P2M_GlobalTheory_deuringCurve___056d131758c7 (a b : R) : (deuringCurve a b).Δ = b ^ 3 * (a ^ 3 - 27 * b) := by sorry

alias «GlobalTheory».«deuringCurve_Δ» := P2M_GlobalTheory_deuringCurve___056d131758c7
