-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__base_510735d22679
-- name    : P2M_Formalism_GM_FrozenVariableComponents_coeff__base_510735d22679
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:18.310324+00:00
-- url     : https://prove2.me/theorems/8434ec8f-4044-4104-a7ad-b47cb948bb61
-- title:
--   P2 M Formalism GM Frozen Variable Components coeff  base 510735d22679: P2 M Formalism GM Frozen Variable Components coeff  base 510735d22679
-- statement:
--   The P2 M Formalism GM Frozen Variable Components coeff  base 510735d22679 construction uses the P2 M Formalism GM Frozen Variable Components coeff  base 510735d22679 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L783-L795
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L783-L795

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

theorem P2M_Formalism_GM_FrozenVariableComponents_coeff__base_510735d22679 (LL : Letters N) (ρ : Fin r) (t : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    coeffη (Finsupp.single ρ t) (aeval (freezeSub p LL ρ) f) = homogeneousComponent t f := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«coeffη_base» := P2M_Formalism_GM_FrozenVariableComponents_coeff__base_510735d22679
