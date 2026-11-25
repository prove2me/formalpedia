-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__kill_e9f2b61ea33a
-- name    : P2M_Formalism_GM_FrozenVariableComponents_coeff__kill_e9f2b61ea33a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:28.723471+00:00
-- url     : https://prove2.me/theorems/5d1885f3-04f7-4b0d-9c59-d7686e2d47e8
-- title:
--   P2 M Formalism GM Frozen Variable Components coeff  kill e9f2b61ea33a: P2 M Formalism GM Frozen Variable Components coeff  kill e9f2b61ea33a
-- statement:
--   The P2 M Formalism GM Frozen Variable Components coeff  kill e9f2b61ea33a construction uses the P2 M Formalism GM Frozen Variable Components coeff  kill e9f2b61ea33a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L720-L732
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L720-L732

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem P2M_Formalism_GM_FrozenVariableComponents_coeff__kill_e9f2b61ea33a (ρ : Fin r) (t : ℕ) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    coeffη (Finsupp.single ρ t) (kill p ρ G) = coeffη (Finsupp.single ρ t) G := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«coeffη_kill» := P2M_Formalism_GM_FrozenVariableComponents_coeff__kill_e9f2b61ea33a
