-- Prove2me | Theorems.Thm_PI_TameSurjW_liesOver_span_iff
-- name    : PI.TameSurjW.liesOver_span_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:29:23.111268+00:00
-- url     : https://prove2.me/theorems/48675eac-8594-5b64-81bb-07ea637002b0
-- title:
--   Tame Surj W: lies Over span iff
-- statement:
--   The Tame Surj W construction uses the lies Over span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TameSurjectivity/RecUnram.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TameSurjectivity/RecUnram.lean#L10-L23

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

theorem PI.TameSurjW.liesOver_span_iff {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    P.LiesOver (Ideal.span {(p : ℤ)}) ↔ ((p : ℕ) : 𝓞 E) ∈ P := by sorry
