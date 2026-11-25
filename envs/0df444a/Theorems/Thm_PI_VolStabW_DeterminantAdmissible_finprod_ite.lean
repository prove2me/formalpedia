-- Prove2me | Theorems.Thm_PI_VolStabW_DeterminantAdmissible_finprod_ite
-- name    : PI.VolStabW.DeterminantAdmissible.finprod_ite
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:43:12.405972+00:00
-- url     : https://prove2.me/theorems/7d234df2-d9be-48d7-b0c4-d0c86ad03e60
-- title:
--   Determinant Admissible: finprod ite
-- statement:
--   The Determinant Admissible construction uses the finprod ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmC.lean#L103-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmC.lean#L103-L114

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC
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
  PI.VolStabW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ}
variable {b}

theorem PI.VolStabW.DeterminantAdmissible.finprod_ite {α : Type} (P : α → Prop) [DecidablePred P] [Decidable (∀ v, P v)] (h : ∀ᶠ v in cofinite, P v) :
    ∏ᶠ v, (if P v then (1 : ℂ) else 0) = if ∀ v, P v then 1 else 0 := by sorry
