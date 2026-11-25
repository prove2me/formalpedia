-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_zero_bf4af767eaba
-- name    : P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_zero_bf4af767eaba
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:26.266247+00:00
-- url     : https://prove2.me/theorems/a0ab5721-10b1-4b09-877a-43c1377e8691
-- title:
--   P2 M Formalism GM Frozen Variable Components coeff  shift zero bf4af767eaba: P2 M Formalism GM Frozen Variable Components coeff  shift zero bf4af767eaba
-- statement:
--   The P2 M Formalism GM Frozen Variable Components coeff  shift zero bf4af767eaba construction uses the P2 M Formalism GM Frozen Variable Components coeff  shift zero bf4af767eaba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L205-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L205-L212

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

theorem P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_zero_bf4af767eaba (b : Fin r →₀ ℕ) (ρ : Fin r) (k : ℕ) (hb : ¬ Finsupp.single ρ k ≤ b)
    (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη b (X (Fin.last N, ρ) ^ k * G) = 0 := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«coeffη_shift_zero» := P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_zero_bf4af767eaba
