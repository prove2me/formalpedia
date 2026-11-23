-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_ev_two
-- name    : PI.GalTorsConj.W.ZetaDoubling.ev_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:14.452208+00:00
-- url     : https://prove2.me/theorems/5b70138c-4efe-41a2-a6c7-1f9181440c95
-- title:
--   Zeta Doubling: ev two
-- statement:
--   The Zeta Doubling construction uses the ev two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddDbl.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddDbl.lean#L23-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
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
open PI.GalTorsConj.W.ZetaDoubling
open OriginCoordinatesAdd

theorem PI.GalTorsConj.W.ZetaDoubling.ev_two (L : PeriodPair) {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ∀ᶠ z' in 𝓝 z, 2 * z' ∉ L.lattice := by sorry
