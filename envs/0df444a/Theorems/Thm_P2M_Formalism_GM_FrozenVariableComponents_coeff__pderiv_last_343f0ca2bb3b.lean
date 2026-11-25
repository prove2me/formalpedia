-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__pderiv_last_343f0ca2bb3b
-- name    : P2M_Formalism_GM_FrozenVariableComponents_coeff__pderiv_last_343f0ca2bb3b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:25.583385+00:00
-- url     : https://prove2.me/theorems/7a77bacc-f4ba-4ece-ad03-4692643977b6
-- title:
--   P2 M Formalism GM Frozen Variable Components coeff  pderiv last 343f0ca2bb3b: P2 M Formalism GM Frozen Variable Components coeff  pderiv last 343f0ca2bb3b
-- statement:
--   The P2 M Formalism GM Frozen Variable Components coeff  pderiv last 343f0ca2bb3b construction uses the P2 M Formalism GM Frozen Variable Components coeff  pderiv last 343f0ca2bb3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L214-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L214-L236

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

theorem P2M_Formalism_GM_FrozenVariableComponents_coeff__pderiv_last_343f0ca2bb3b (b : Fin r →₀ ℕ) (c : Fin r) (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη b (pderiv (Fin.last N, c) G) = ((b c + 1 : ℕ) : K) • coeffη (b + Finsupp.single c 1) G := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«coeffη_pderiv_last» := P2M_Formalism_GM_FrozenVariableComponents_coeff__pderiv_last_343f0ca2bb3b
