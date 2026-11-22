-- Prove2me | Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_norm_natCast_le_one__a9d2d1dd10a2
-- name    : P2M_Formalism_GM_gammaIntegralityLemmas_norm_natCast_le_one__a9d2d1dd10a2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:41.386833+00:00
-- url     : https://prove2.me/theorems/fcc46b9b-0864-455a-a034-1eb7bc714f2a
-- title:
--   P2 M Formalism GM gamma Integrality Lemmas norm nat Cast le one  a9d2d1dd10a2: P2 M Formalism GM gamma Integrality Lemmas norm nat Cast le one  a9d2d1dd10a2
-- statement:
--   The P2 M Formalism GM gamma Integrality Lemmas norm nat Cast le one  a9d2d1dd10a2 construction uses the P2 M Formalism GM gamma Integrality Lemmas norm nat Cast le one  a9d2d1dd10a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L13-L15

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem P2M_Formalism_GM_gammaIntegralityLemmas_norm_natCast_le_one__a9d2d1dd10a2 (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by sorry

alias «Formalism».«GM».«gammaIntegralityLemmas».«norm_natCast_le_one'» := P2M_Formalism_GM_gammaIntegralityLemmas_norm_natCast_le_one__a9d2d1dd10a2
