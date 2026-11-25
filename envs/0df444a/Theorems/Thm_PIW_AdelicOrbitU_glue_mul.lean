-- Prove2me | Theorems.Thm_PIW_AdelicOrbitU_glue_mul
-- name    : PIW.AdelicOrbitU.glue_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:44.500799+00:00
-- url     : https://prove2.me/theorems/7dce7ee7-8f3e-40d1-a6ba-ca1b73faef5d
-- title:
--   Adelic Orbit U: glue mul
-- statement:
--   The Adelic Orbit U construction uses the glue mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/StLamOf.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/StLamOf.lean#L18-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem PIW.AdelicOrbitU.glue_mul {S : Type} [CommRing S] {k : ℕ} (e : Fin k → S) (hid : ∀ i, e i * e i = e i)
    (hor : ∀ i j, i ≠ j → e i * e j = 0) (X Y : Fin k → S) :
    (∑ i, e i * X i) * (∑ j, e j * Y j) = ∑ i, e i * (X i * Y i) := by sorry
