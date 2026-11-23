-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_360bf627fe39
-- name    : P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_360bf627fe39
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:24.450341+00:00
-- url     : https://prove2.me/theorems/3e0349ec-e58b-4927-846a-936bf5765d25
-- title:
--   P2 M Formalism GM Frozen Variable Components coeff  shift 360bf627fe39: P2 M Formalism GM Frozen Variable Components coeff  shift 360bf627fe39
-- statement:
--   The P2 M Formalism GM Frozen Variable Components coeff  shift 360bf627fe39 construction uses the P2 M Formalism GM Frozen Variable Components coeff  shift 360bf627fe39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L198-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L198-L203

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

theorem P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_360bf627fe39 (b : Fin r →₀ ℕ) (ρ : Fin r) (k : ℕ) (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη (b + Finsupp.single ρ k) (X (Fin.last N, ρ) ^ k * G) = coeffη b G := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«coeffη_shift» := P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_360bf627fe39
