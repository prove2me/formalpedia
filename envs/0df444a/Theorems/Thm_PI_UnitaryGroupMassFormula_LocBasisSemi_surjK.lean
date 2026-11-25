-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocBasisSemi_surjK
-- name    : PI.UnitaryGroupMassFormula.LocBasisSemi.surjK
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:55.562802+00:00
-- url     : https://prove2.me/theorems/b165f0ef-735b-430d-8dea-5b9802692cbf
-- title:
--   Loc Basis Semi: surj K
-- statement:
--   The Loc Basis Semi construction uses the surj K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemilocalBasis/SmulMemOfMemSpan.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemilocalBasis/SmulMemOfMemSpan.lean#L40-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisSemi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemilocalBasis_SmulMemOfMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocBasisSemi
variable (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
variable {K p}

theorem PI.UnitaryGroupMassFormula.LocBasisSemi.surjK (a : A K p) : ∃ s : ℕ, Nat.Coprime s p ∧ ∃ x : 𝓞 K, (s : K) * (a : K) = (x : K) := by sorry
