-- Prove2me | Theorems.Thm_P2M_GlobalTheory_legendreCurve_c__2f3c0f8196e8
-- name    : P2M_GlobalTheory_legendreCurve_c__2f3c0f8196e8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:00.383115+00:00
-- url     : https://prove2.me/theorems/c80e1e46-8f3b-52d4-94b4-ce8bbe0d413d
-- title:
--   P2 M Global Theory legendre Curve c  2f3c0f8196e8: P2 M Global Theory legendre Curve c  2f3c0f8196e8
-- statement:
--   The P2 M Global Theory legendre Curve c  2f3c0f8196e8 construction uses the P2 M Global Theory legendre Curve c  2f3c0f8196e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L79-L80

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

theorem P2M_GlobalTheory_legendreCurve_c__2f3c0f8196e8 (l : R) : (legendreCurve l).c₄ = 16 * (l ^ 2 - l + 1) := by sorry

alias «GlobalTheory».«legendreCurve_c₄» := P2M_GlobalTheory_legendreCurve_c__2f3c0f8196e8
