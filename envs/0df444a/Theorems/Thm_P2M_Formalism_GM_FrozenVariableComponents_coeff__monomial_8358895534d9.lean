-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__monomial_8358895534d9
-- name    : P2M_Formalism_GM_FrozenVariableComponents_coeff__monomial_8358895534d9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:56.383798+00:00
-- url     : https://prove2.me/theorems/7bb24650-8dcb-43d3-ba71-119564d7f264
-- title:
--   P2 M Formalism GM Frozen Variable Components coeff  monomial 8358895534d9: P2 M Formalism GM Frozen Variable Components coeff  monomial 8358895534d9
-- statement:
--   The P2 M Formalism GM Frozen Variable Components coeff  monomial 8358895534d9 construction uses the P2 M Formalism GM Frozen Variable Components coeff  monomial 8358895534d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L124-L127

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

theorem P2M_Formalism_GM_FrozenVariableComponents_coeff__monomial_8358895534d9 (b : Fin r →₀ ℕ) (m : Fin (N + 1) × Fin r →₀ ℕ) (a : K) :
    coeffη b (monomial m a) = if etaPart m = b then monomial (llPart m) a else 0 := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«coeffη_monomial» := P2M_Formalism_GM_FrozenVariableComponents_coeff__monomial_8358895534d9
