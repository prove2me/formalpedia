-- Prove2me | Theorems.Thm_PI_HeckeProdW_pw_infDiag
-- name    : PI.HeckeProdW.pw_infDiag
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:31:27.989665+00:00
-- url     : https://prove2.me/theorems/da7b98cb-394f-4e27-9ddd-4f1829d6809f
-- title:
--   Hecke Prod W: pw inf Diag
-- statement:
--   The Hecke Prod W construction uses the pw inf Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L96-L102

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct
open PI PI.HeckeProdW
variable {L : Type} [Field L] [NumberField L]

theorem PI.HeckeProdW.pw_infDiag (w : InfinitePlace L) (k : Lˣ) : pw w (infDiag k) = (atInf w k : w.Completion) := by sorry
