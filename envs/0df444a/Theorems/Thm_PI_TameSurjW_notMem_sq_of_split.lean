-- Prove2me | Theorems.Thm_PI_TameSurjW_notMem_sq_of_split
-- name    : PI.TameSurjW.notMem_sq_of_split
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:29:53.376902+00:00
-- url     : https://prove2.me/theorems/11b9afd2-061d-498a-8897-7e196b0be587
-- title:
--   Tame Surj W: not Mem sq of split
-- statement:
--   The Tame Surj W construction uses the not Mem sq of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TameSurjectivity/RecUnram.lean#L25-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TameSurjectivity/RecUnram.lean#L25-L70

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TameSurjectivity_RecUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open PI PI.TameSurjW

theorem PI.TameSurjW.notMem_sq_of_split {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ Formalism.BasicNotions.placesOver E p) :
    ((p : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 := by sorry
