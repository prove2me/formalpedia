-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_alp_last
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.alp_last
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:48:28.626418+00:00
-- url     : https://prove2.me/theorems/27d4e36d-ad53-4d37-ba9d-2fa6d198d39f
-- title:
--   Loc Jac Typ: alp last
-- statement:
--   The Loc Jac Typ construction uses the alp last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitAbs.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitAbs.lean#L80-L82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
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
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.UnitaryGroupMassFormula.LocJacTyp.alp_last (r : ℕ) : alp v r (Fin.last r) = 1 := by sorry
