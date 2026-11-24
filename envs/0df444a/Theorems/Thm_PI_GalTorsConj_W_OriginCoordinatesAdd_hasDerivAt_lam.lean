-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_hasDerivAt_lam
-- name    : PI.GalTorsConj.W.OriginCoordinatesAdd.hasDerivAt_lam
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:05.035314+00:00
-- url     : https://prove2.me/theorems/ecc0ceff-7ba5-497d-893c-13bbce6230cc
-- title:
--   Origin Coordinates Add: has Deriv At lam
-- statement:
--   The Origin Coordinates Add construction uses the has Deriv At lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddLaw.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddLaw.lean#L26-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
open Filter Topology
open PI.GalTorsConj.W.OriginCoordinatesAdd

theorem PI.GalTorsConj.W.OriginCoordinatesAdd.hasDerivAt_lam (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice)
    (hne : L.weierstrassP z - L.weierstrassP w ≠ 0) :
    HasDerivAt (lam L w)
      (((6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (L.weierstrassP z - L.weierstrassP w)
        - (L.derivWeierstrassP z - L.derivWeierstrassP w) * L.derivWeierstrassP z)
        / (L.weierstrassP z - L.weierstrassP w) ^ 2) z := by sorry
