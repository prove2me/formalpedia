-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_prod
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.absV_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:02.250882+00:00
-- url     : https://prove2.me/theorems/3c83ad32-17e1-5655-b55e-0de64490376b
-- title:
--   Loc Jac Typ: abs V prod
-- statement:
--   The Loc Jac Typ construction uses the abs V prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L217-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L217-L219

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.UnitaryGroupMassFormula.LocJacTyp.absV_prod {ι : Type} (s : Finset ι) (f : ι → Fv F v) :
    absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) := by sorry
