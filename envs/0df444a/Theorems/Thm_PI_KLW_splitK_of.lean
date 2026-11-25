-- Prove2me | Theorems.Thm_PI_KLW_splitK_of
-- name    : PI.KLW.splitK_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:33:09.02229+00:00
-- url     : https://prove2.me/theorems/e46fe7b0-a49f-417a-9958-aafbc085ad3e
-- title:
--   KLW: split K of
-- statement:
--   The KLW construction uses the split K of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L92-L95

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem PI.KLW.splitK_of (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) {p : ℕ}
    (hs : PI.KerIso.SplitsAt K cj p) : SplitK (conjK cj hc.2.1) p := by sorry
