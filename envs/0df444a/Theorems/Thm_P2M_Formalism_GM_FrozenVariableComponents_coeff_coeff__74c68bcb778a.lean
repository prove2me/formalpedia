-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff__74c68bcb778a
-- name    : P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff__74c68bcb778a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:33.042801+00:00
-- url     : https://prove2.me/theorems/7c0662aa-a091-464d-9b78-e5a9baa5a3b8
-- title:
--   P2 M Formalism GM Frozen Variable Components coeff coeff  74c68bcb778a: P2 M Formalism GM Frozen Variable Components coeff coeff  74c68bcb778a
-- statement:
--   The P2 M Formalism GM Frozen Variable Components coeff coeff  74c68bcb778a construction uses the P2 M Formalism GM Frozen Variable Components coeff coeff  74c68bcb778a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L145-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L145-L147

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
open MvPolynomial Finset
variable {K : Type*} [CommRing K] {N r : ℕ}

theorem P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff__74c68bcb778a (m : Fin (N + 1) × Fin r →₀ ℕ) (F : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeff (llPart m) (coeffη (etaPart m) F) = coeff m F := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«coeff_coeffη» := P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff__74c68bcb778a
