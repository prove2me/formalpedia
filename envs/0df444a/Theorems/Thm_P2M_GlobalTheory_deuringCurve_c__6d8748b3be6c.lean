-- Prove2me | Theorems.Thm_P2M_GlobalTheory_deuringCurve_c__6d8748b3be6c
-- name    : P2M_GlobalTheory_deuringCurve_c__6d8748b3be6c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:11:58.115023+00:00
-- url     : https://prove2.me/theorems/5f49652c-f2f2-4a28-8fef-71fe034c223e
-- title:
--   P2 M Global Theory deuring Curve c  6d8748b3be6c: P2 M Global Theory deuring Curve c  6d8748b3be6c
-- statement:
--   The P2 M Global Theory deuring Curve c  6d8748b3be6c construction uses the P2 M Global Theory deuring Curve c  6d8748b3be6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L85-L86

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

theorem P2M_GlobalTheory_deuringCurve_c__6d8748b3be6c (a b : R) : (deuringCurve a b).c₄ = a * (a ^ 3 - 24 * b) := by sorry

alias «GlobalTheory».«deuringCurve_c₄» := P2M_GlobalTheory_deuringCurve_c__6d8748b3be6c
