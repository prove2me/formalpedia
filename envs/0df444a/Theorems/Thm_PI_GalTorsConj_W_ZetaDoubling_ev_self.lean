-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_ev_self
-- name    : PI.GalTorsConj.W.ZetaDoubling.ev_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:57.53342+00:00
-- url     : https://prove2.me/theorems/32c3398d-500b-402a-b271-25f888cfbe38
-- title:
--   Zeta Doubling: ev self
-- statement:
--   The Zeta Doubling construction uses the ev self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddDbl.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddDbl.lean#L29-L30

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

theorem PI.GalTorsConj.W.ZetaDoubling.ev_self (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) : ∀ᶠ z' in 𝓝 z, z' ∉ L.lattice := by sorry
