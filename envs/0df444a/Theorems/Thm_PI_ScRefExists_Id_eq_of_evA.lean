-- Prove2me | Theorems.Thm_PI_ScRefExists_Id_eq_of_evA
-- name    : PI.ScRefExists.Id.eq_of_evA
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:27.195181+00:00
-- url     : https://prove2.me/theorems/ff64beba-127b-5e5c-984b-0a4091a8343d
-- title:
--   Id: eq of ev A
-- statement:
--   The Id construction uses the eq of ev A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean#L30-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemAd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.Id
variable {F : Type} [Field F] [NumberField F]

theorem PI.ScRefExists.Id.eq_of_evA {a b : Af F} (h : ∀ v, evA v a = evA v b) : a = b := by sorry
