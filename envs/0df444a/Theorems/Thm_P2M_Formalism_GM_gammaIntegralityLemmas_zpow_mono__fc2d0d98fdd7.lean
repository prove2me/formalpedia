-- Prove2me | Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_zpow_mono__fc2d0d98fdd7
-- name    : P2M_Formalism_GM_gammaIntegralityLemmas_zpow_mono__fc2d0d98fdd7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:59.370977+00:00
-- url     : https://prove2.me/theorems/f30b79e7-0140-44e2-a43a-be7e67444ef3
-- title:
--   P2 M Formalism GM gamma Integrality Lemmas zpow mono  fc2d0d98fdd7: P2 M Formalism GM gamma Integrality Lemmas zpow mono  fc2d0d98fdd7
-- statement:
--   The P2 M Formalism GM gamma Integrality Lemmas zpow mono  fc2d0d98fdd7 construction uses the P2 M Formalism GM gamma Integrality Lemmas zpow mono  fc2d0d98fdd7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L246-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L246-L247

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

theorem P2M_Formalism_GM_gammaIntegralityLemmas_zpow_mono__fc2d0d98fdd7 {a b : ℤ} (h : a ≤ b) : (p : ℝ) ^ a ≤ (p : ℝ) ^ b := by sorry

alias «Formalism».«GM».«gammaIntegralityLemmas».«zpow_mono'» := P2M_Formalism_GM_gammaIntegralityLemmas_zpow_mono__fc2d0d98fdd7
