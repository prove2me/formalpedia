-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocBasisSemi_common_denom
-- name    : PI.UnitaryGroupMassFormula.LocBasisSemi.common_denom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:34.178463+00:00
-- url     : https://prove2.me/theorems/98a974bf-f9dd-5622-90c2-161f60900c16
-- title:
--   Loc Basis Semi: common denom
-- statement:
--   The Loc Basis Semi construction uses the common denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemilocalBasis/SmulMemOfMemSpan.lean#L51-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemilocalBasis/SmulMemOfMemSpan.lean#L51-L63

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

theorem PI.UnitaryGroupMassFormula.LocBasisSemi.common_denom {ι : Type*} [Fintype ι] (c : ι → A K p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ x : ι → 𝓞 K, ∀ i, (s : K) * (c i : K) = (x i : K) := by sorry
