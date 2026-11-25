-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_ev_adm
-- name    : PI.GalTorsConj.W.OriginCoordinatesAdd.ev_adm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:24.810717+00:00
-- url     : https://prove2.me/theorems/536e4a88-f2cc-48a3-b34f-a012ef2a25b9
-- title:
--   Origin Coordinates Add: ev adm
-- statement:
--   The Origin Coordinates Add construction uses the ev adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddLaw.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddLaw.lean#L46-L52

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

theorem PI.GalTorsConj.W.OriginCoordinatesAdd.ev_adm (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hm : z - w ∉ L.lattice)
    (hp : z + w ∉ L.lattice) :
    ∀ᶠ z' in 𝓝 z, z' ∉ L.lattice ∧ z' - w ∉ L.lattice ∧ z' + w ∉ L.lattice := by sorry
