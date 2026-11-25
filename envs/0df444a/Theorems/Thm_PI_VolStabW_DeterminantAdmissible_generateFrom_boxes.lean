-- Prove2me | Theorems.Thm_PI_VolStabW_DeterminantAdmissible_generateFrom_boxes
-- name    : PI.VolStabW.DeterminantAdmissible.generateFrom_boxes
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:46:19.457119+00:00
-- url     : https://prove2.me/theorems/2d40cbec-36f9-5c3e-b0d0-64bf6de3ea17
-- title:
--   Determinant Admissible: generate From boxes
-- statement:
--   The Determinant Admissible construction uses the generate From boxes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmB.lean#L201-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmB.lean#L201-L225

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

theorem PI.VolStabW.DeterminantAdmissible.generateFrom_boxes : generateFrom (boxes F ι) = (MeasurableSpace.pi : MeasurableSpace (ι → Af F)) := by sorry
