-- Prove2me | Theorems.Thm_PI_IsoFunVW_minY_map
-- name    : PI.IsoFunVW.minY_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:42.296628+00:00
-- url     : https://prove2.me/theorems/4cca0cf2-4949-41bf-912a-19afd9ce5029
-- title:
--   Iso Fun VW: min Y map
-- statement:
--   The Iso Fun VW construction uses the min Y map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L56-L60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoFunV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MvPolynomial
noncomputable section
open PI PI.IsoFunVW
open PI.IsoFunV

theorem PI.IsoFunVW.minY_map {Lt k k' : Type} [Fintype Lt] [CommRing k] [CommRing k'] (f : k →+* k')
    (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu) (y : Lt → Fin N → ℕ → k) :
    f (minY N nu J y) = minY N nu J (fun z a j => f (y z a j)) := by sorry
