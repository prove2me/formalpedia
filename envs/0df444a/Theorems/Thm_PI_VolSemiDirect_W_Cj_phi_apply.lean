-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_phi_apply
-- name    : PI.VolSemiDirect.W.Cj.phi_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:58.190919+00:00
-- url     : https://prove2.me/theorems/8d5b198d-f6b4-4d20-a01f-01a3cca2486b
-- title:
--   Cj: phi apply
-- statement:
--   The Cj construction uses the phi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/MapPhiOfModM.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/MapPhiOfModM.lean#L31-L32

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

theorem PI.VolSemiDirect.W.Cj.phi_apply (X : GL (Fin k) A) (v : Fin k → A) :
    phi X v = (X : Matrix (Fin k) (Fin k) A).mulVec v := by sorry
