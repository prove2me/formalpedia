-- Prove2me | Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_norm_intCast_le_one__7a067930451d
-- name    : P2M_Formalism_GM_gammaIntegralityLemmas_norm_intCast_le_one__7a067930451d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:23.492183+00:00
-- url     : https://prove2.me/theorems/b4594d38-8f05-4bfb-b3bd-766500872382
-- title:
--   P2 M Formalism GM gamma Integrality Lemmas norm int Cast le one  7a067930451d: P2 M Formalism GM gamma Integrality Lemmas norm int Cast le one  7a067930451d
-- statement:
--   The P2 M Formalism GM gamma Integrality Lemmas norm int Cast le one  7a067930451d construction uses the P2 M Formalism GM gamma Integrality Lemmas norm int Cast le one  7a067930451d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L17-L18

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

theorem P2M_Formalism_GM_gammaIntegralityLemmas_norm_intCast_le_one__7a067930451d (n : ℤ) : ‖(n : ℚ_[p])‖ ≤ 1 := by sorry

alias «Formalism».«GM».«gammaIntegralityLemmas».«norm_intCast_le_one'» := P2M_Formalism_GM_gammaIntegralityLemmas_norm_intCast_le_one__7a067930451d
