-- Prove2me | Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_zpow_pos__da61b7487fff
-- name    : P2M_Formalism_GM_gammaIntegralityLemmas_zpow_pos__da61b7487fff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:43.080428+00:00
-- url     : https://prove2.me/theorems/563860ec-fada-4bc1-ac24-b4fa0009fba0
-- title:
--   P2 M Formalism GM gamma Integrality Lemmas zpow pos  da61b7487fff: P2 M Formalism GM gamma Integrality Lemmas zpow pos  da61b7487fff
-- statement:
--   The P2 M Formalism GM gamma Integrality Lemmas zpow pos  da61b7487fff construction uses the P2 M Formalism GM gamma Integrality Lemmas zpow pos  da61b7487fff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L249-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L249-L250

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
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_Formalism_GM_gammaIntegralityLemmas_zpow_pos__da61b7487fff (a : ℤ) : (0 : ℝ) < (p : ℝ) ^ a := by sorry

alias «Formalism».«GM».«gammaIntegralityLemmas».«zpow_pos'» := P2M_Formalism_GM_gammaIntegralityLemmas_zpow_pos__da61b7487fff
