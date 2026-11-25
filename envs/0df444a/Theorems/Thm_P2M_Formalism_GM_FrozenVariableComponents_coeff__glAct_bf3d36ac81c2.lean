-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__glAct_bf3d36ac81c2
-- name    : P2M_Formalism_GM_FrozenVariableComponents_coeff__glAct_bf3d36ac81c2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:16.996081+00:00
-- url     : https://prove2.me/theorems/982e1b9c-b2c7-4ebd-ace3-61731da14c97
-- title:
--   P2 M Formalism GM Frozen Variable Components coeff  gl Act bf3d36ac81c2: P2 M Formalism GM Frozen Variable Components coeff  gl Act bf3d36ac81c2
-- statement:
--   The P2 M Formalism GM Frozen Variable Components coeff  gl Act bf3d36ac81c2 construction uses the P2 M Formalism GM Frozen Variable Components coeff  gl Act bf3d36ac81c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L271-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L271-L278

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

theorem P2M_Formalism_GM_FrozenVariableComponents_coeff__glAct_bf3d36ac81c2 (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (c d : Fin r) (b : Fin r →₀ ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    coeffη b (glAct p (LL.snoc n) j c d F) = glAct p LL j c d (coeffη b F) := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«coeffη_glAct» := P2M_Formalism_GM_FrozenVariableComponents_coeff__glAct_bf3d36ac81c2
