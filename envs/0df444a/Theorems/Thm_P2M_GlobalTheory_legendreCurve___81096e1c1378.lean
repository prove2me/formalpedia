-- Prove2me | Theorems.Thm_P2M_GlobalTheory_legendreCurve___81096e1c1378
-- name    : P2M_GlobalTheory_legendreCurve___81096e1c1378
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:09.290522+00:00
-- url     : https://prove2.me/theorems/afc78be4-8d60-46d1-bc46-0747c136b576
-- title:
--   P2 M Global Theory legendre Curve   81096e1c1378: P2 M Global Theory legendre Curve   81096e1c1378
-- statement:
--   The P2 M Global Theory legendre Curve   81096e1c1378 construction uses the P2 M Global Theory legendre Curve   81096e1c1378 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L76-L77

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

theorem P2M_GlobalTheory_legendreCurve___81096e1c1378 (l : R) : (legendreCurve l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 := by sorry

alias «GlobalTheory».«legendreCurve_Δ» := P2M_GlobalTheory_legendreCurve___81096e1c1378
