-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_map_phi_of_modM
-- name    : PI.VolSemiDirect.W.Cj.map_phi_of_modM
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:36.956718+00:00
-- url     : https://prove2.me/theorems/2541c24e-1e24-49e8-9bb6-7213d13892fb
-- title:
--   Cj: map phi of mod M
-- statement:
--   The Cj construction uses the map phi of mod M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/MapPhiOfModM.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/MapPhiOfModM.lean#L55-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAFTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open MeasureTheory Measure
open scoped NNReal
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}

theorem PI.VolSemiDirect.W.Cj.map_phi_of_modM (X : GL (Fin k) A) (hX : modM X = 1) (μ : Measure (Fin k → A))
    [μ.IsAddHaarMeasure] : μ.map (phi X) = μ := by sorry
