-- Prove2me | Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_Odd_map_dualM
-- name    : PI.BlockRatReal.UnitaryGroupMassFormula.Odd.map_dualM
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:51.421451+00:00
-- url     : https://prove2.me/theorems/6e412148-cf00-5b86-9da8-036b0473a7f5
-- title:
--   Odd: map dual M
-- statement:
--   The Odd construction uses the map dual M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/MapDetGenM.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/MapDetGenM.lean#L18-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_OddDualWeylFactorization
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_MapDetGenM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal PI.BlockRatReal.UnitaryGroupMassFormula PI.BlockRatReal.UnitaryGroupMassFormula.Odd
open PI.OddDualWeyl

theorem PI.BlockRatReal.UnitaryGroupMassFormula.Odd.map_dualM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) (i j : Fin k) :
    MvPolynomial.map φ (dualM R k i j) = dualM S k i j := by sorry
