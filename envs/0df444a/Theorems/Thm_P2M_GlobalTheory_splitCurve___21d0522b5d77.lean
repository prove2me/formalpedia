-- Prove2me | Theorems.Thm_P2M_GlobalTheory_splitCurve___21d0522b5d77
-- name    : P2M_GlobalTheory_splitCurve___21d0522b5d77
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:51.57123+00:00
-- url     : https://prove2.me/theorems/bf86b1dd-cf04-4f4d-9755-e5a026561f3b
-- title:
--   P2 M Global Theory split Curve   21d0522b5d77: P2 M Global Theory split Curve   21d0522b5d77
-- statement:
--   The P2 M Global Theory split Curve   21d0522b5d77 construction uses the P2 M Global Theory split Curve   21d0522b5d77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L70-L71

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

theorem P2M_GlobalTheory_splitCurve___21d0522b5d77 (A B : R) : (splitCurve A B).Δ = 16 * A ^ 2 * B ^ 2 * (A - B) ^ 2 := by sorry

alias «GlobalTheory».«splitCurve_Δ» := P2M_GlobalTheory_splitCurve___21d0522b5d77
