-- Prove2me | Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_Odd_map_dualSub
-- name    : PI.BlockRatReal.UnitaryGroupMassFormula.Odd.map_dualSub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:26:38.745036+00:00
-- url     : https://prove2.me/theorems/264de012-f2ca-5e7d-8bd9-02832e408c35
-- title:
--   Odd: map dual Sub
-- statement:
--   The Odd construction uses the map dual Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/MapDetGenM.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/MapDetGenM.lean#L28-L38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_OddDualWeylFactorization
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_MapDetGenM
import Theorems.Thm_PI_OddDualWeyl_Red_map_dualSub

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

theorem PI.BlockRatReal.UnitaryGroupMassFormula.Odd.map_dualSub {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ)
    (p : MvPolynomial (Fin k × Fin k) R) :
    MvPolynomial.map φ (dualSub R k p) = dualSub S k (MvPolynomial.map φ p) := by sorry
