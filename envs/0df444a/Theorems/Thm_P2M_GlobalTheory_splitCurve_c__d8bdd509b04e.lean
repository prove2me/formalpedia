-- Prove2me | Theorems.Thm_P2M_GlobalTheory_splitCurve_c__d8bdd509b04e
-- name    : P2M_GlobalTheory_splitCurve_c__d8bdd509b04e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:44.19631+00:00
-- url     : https://prove2.me/theorems/024bdc43-7099-4770-882c-426169f8619e
-- title:
--   P2 M Global Theory split Curve c  d8bdd509b04e: P2 M Global Theory split Curve c  d8bdd509b04e
-- statement:
--   The P2 M Global Theory split Curve c  d8bdd509b04e construction uses the P2 M Global Theory split Curve c  d8bdd509b04e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L73-L74

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

theorem P2M_GlobalTheory_splitCurve_c__d8bdd509b04e (A B : R) : (splitCurve A B).c₄ = 16 * (A ^ 2 - A * B + B ^ 2) := by sorry

alias «GlobalTheory».«splitCurve_c₄» := P2M_GlobalTheory_splitCurve_c__d8bdd509b04e
