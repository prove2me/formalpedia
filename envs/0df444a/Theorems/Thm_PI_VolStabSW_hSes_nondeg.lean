-- Prove2me | Theorems.Thm_PI_VolStabSW_hSes_nondeg
-- name    : PI.VolStabSW.hSes_nondeg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:37:56.731662+00:00
-- url     : https://prove2.me/theorems/c76b68e3-f9d9-40a7-912c-f5fe96936499
-- title:
--   Vol Stab SW: h Ses nondeg
-- statement:
--   The Vol Stab SW construction uses the h Ses nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/HformSmulRight.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/HformSmulRight.lean#L62-L72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HformSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
variable {E : Type} [Field E] {M : ℕ}
variable [StarRing E]

theorem PI.VolStabSW.hSes_nondeg (J : Matrix (Fin M) (Fin M) E) (hdet : J.det ≠ 0) (x : Fin M → E)
    (hx : ∀ y, hSes J x y = 0) : x = 0 := by sorry
