-- Prove2me | Theorems.Thm_PI_LocLatEq_W_core_smem
-- name    : PI.LocLatEq.W.core_smem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:34:53.180799+00:00
-- url     : https://prove2.me/theorems/2cf5d953-2fb7-58fe-8f39-2268deb4220f
-- title:
--   W: core smem
-- statement:
--   The W construction uses the core smem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/CoreFgOfLe.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/CoreFgOfLe.lean#L39-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreGenIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreFgOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocLatEq PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem PI.LocLatEq.W.core_smem (A : LocAt F E sig p) {n : ℕ} (S : Submodule A.O (Fin n → A.Ep)) {o : A.Ep}
    (ho : o ∈ A.O) {x : Fin n → A.Ep} (hx : x ∈ S) : o • x ∈ S := by sorry
