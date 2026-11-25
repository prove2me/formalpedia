-- Prove2me | Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_Odd_map_det_genM
-- name    : PI.BlockRatReal.UnitaryGroupMassFormula.Odd.map_det_genM
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:26:30.965635+00:00
-- url     : https://prove2.me/theorems/1a511745-a739-4601-b982-1f55f5bf638f
-- title:
--   Odd: map det gen M
-- statement:
--   The Odd construction uses the map det gen M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/MapDetGenM.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/MapDetGenM.lean#L24-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_OddDualWeylFactorization
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_MapDetGenM
import Theorems.Thm_PI_OddDualWeyl_Red_map_det_genM

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

theorem PI.BlockRatReal.UnitaryGroupMassFormula.Odd.map_det_genM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) :
    MvPolynomial.map φ (genM R k).det = (genM S k).det := by sorry
