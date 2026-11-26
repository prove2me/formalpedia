-- Prove2me | Theorems.Thm_PI_WAU_coord_smul
-- name    : PI.WAU.coord_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:00.019808+00:00
-- url     : https://prove2.me/theorems/a9cf2e0c-6c62-4749-83b7-875a1df8c2b4
-- title:
--   WAU: coord smul
-- statement:
--   The WAU construction uses the coord smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CoordTmulOneMul.lean#L53-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CoordTmulOneMul.lean#L53-L53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open scoped TensorProduct
variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

theorem PI.WAU.coord_smul (c : F) (x : E ⊗[F] B) : coord b (c • x) = c • coord b x := by sorry
