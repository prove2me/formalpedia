-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__X_castSucc_mul_a41a5a9118e3
-- name    : P2M_Formalism_GM_FrozenVariableComponents_coeff__X_castSucc_mul_a41a5a9118e3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:39.872426+00:00
-- url     : https://prove2.me/theorems/be3c0534-52c4-40a4-a084-381108181dcd
-- title:
--   P2 M Formalism GM Frozen Variable Components coeff  X cast Succ mul a41a5a9118e3: P2 M Formalism GM Frozen Variable Components coeff  X cast Succ mul a41a5a9118e3
-- statement:
--   The P2 M Formalism GM Frozen Variable Components coeff  X cast Succ mul a41a5a9118e3 construction uses the P2 M Formalism GM Frozen Variable Components coeff  X cast Succ mul a41a5a9118e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L173-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L173-L180

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

theorem P2M_Formalism_GM_FrozenVariableComponents_coeff__X_castSucc_mul_a41a5a9118e3 (b : Fin r →₀ ℕ) (i : Fin N) (c : Fin r)
    (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη b (X (Fin.castSucc i, c) * G) = X (i, c) * coeffη b G := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«coeffη_X_castSucc_mul» := P2M_Formalism_GM_FrozenVariableComponents_coeff__X_castSucc_mul_a41a5a9118e3
